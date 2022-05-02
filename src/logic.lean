
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro hp,
  intro hnp,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro hnnp,
  by_cases P,
  assumption,
  have hboom : false := hnnp h,
  contradiction,

end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  apply doubleneg_elim,
  apply doubleneg_intro,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro hor,
  cases hor with hp hq,
  right,
  assumption,
  left,
  assumption,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro hand,
  cases hand with hp hq,
  split,
  assumption,
  assumption,

end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro hor,
  intro hp,
  cases hor with hnp hq,
  contradiction,
  assumption,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro hor,
  intro hnp,
  cases hor with hp hq,
  contradiction,
  assumption,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro hpq,
  intro hnq,
  intro hp,
  have hq : Q := hpq hp,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro hnqnp,
  intro hp,
  by_contra hnq,
  have hnp : ¬P := hnqnp hnq,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  apply impl_as_contrapositive,
  apply impl_as_contrapositive_converse,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro hnor,
  apply hnor,
  right,
  intro hp,
  apply hnor,
  left,
  assumption,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro hpqp,
  intro hnp,
  apply hnp,
  apply hpqp,
  intro hp,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro hor,
  intro hand,
  cases hand with hnp hnq,
  cases hor with hp hq,
  contradiction,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro hand,
  intro hor,
  cases hand with hp hq,
  cases hor with hnp hnq,
  contradiction,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro hnor,
  split,
  intro hp,
  apply hnor,
  left,
  assumption,
  intro hq,
  apply hnor,
  right,
  assumption,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro hand,
  intro hor,
  cases hand with hnp hnq,
  cases hor with hp hq,
  contradiction,
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro hnand,
  by_contra hnor,
  apply hnand,
  split,
  by_contra hnp,
  apply hnor,
  right,
  assumption,
  by_contra hnq,
  apply hnor,
  left,
  assumption,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro hor,
  intro hand,
  cases hand with hp hq,
  cases hor with hnq hnp,
  contradiction,
  contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  apply demorgan_conj,
  apply demorgan_conj_converse,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  apply demorgan_disj,
  apply demorgan_disj_converse,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro hand,
  cases hand with hp hor,
  cases hor with hq hr,
  left,
  split,
  assumption,
  assumption,
  right,
  split,
  assumption,
  assumption,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro hor,
  cases hor with handpq handpr,
  split,
  cases handpq with hp hq,
  assumption,
  cases handpq with hp hq,
  left,
  assumption,
  split,
  cases handpr with hp hr,
  assumption,
  cases handpr with hp hr,
  right,
  assumption,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro hor,
  cases hor with hp handqr,
  split,
  left,
  assumption,
  left,
  assumption,
  cases handqr with hq hr,
  split,
  right,
  assumption,
  right,
  assumption,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro hand,
  cases hand with horpq horpr,
  cases horpr with hp hr,
  left,
  assumption,
  cases horpq with hp hq,
  left,
  assumption,
  right,
  split,
  assumption,
  assumption,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro handr,
  intro hp,
  intro hq,
  apply handr,
  split,
  assumption,
  assumption,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro hpqr,
  intro hand,
  cases hand with hp hq,
  apply hpqr,
  assumption,
  assumption,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro hp,
  assumption,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro hp,
  left,
  assumption,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro hq,
  right,
  assumption,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro hand,
  cases hand with hp hq,
  assumption,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro hand,
  cases hand with hp hq,
  assumption,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  apply weaken_conj_right,
  intro hp,
  split,
  assumption,
  assumption,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro hor,
  cases hor with hp hp,
  assumption,
  assumption,
  apply weaken_disj_right,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intro hnepx,
  intro x,
  intro hpx,
  apply hnepx,
  existsi x,
  assumption,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intro hforallnpx,
  intro hepx,
  cases hepx with x hpx,
  have hnpx : ¬P x := hforallnpx x,
  contradiction,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro hnforallpx,
  by_contra hnenpx,
  apply hnforallpx,
  intro x,
  by_contra hnpx,
  apply hnenpx,
  existsi x,
  assumption,
  
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intro henpx,
  intro hforallpx,
  cases henpx with x hnpx,
  have hpx : P x := hforallpx x,
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  apply demorgan_forall,
  apply demorgan_forall_converse,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  apply demorgan_exists,
  apply demorgan_exists_converse,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intro hepx,
  intro hforallnpx,
  cases hepx with x hpx,
  have hnpx : ¬P x := hforallnpx x,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intro hforallpx,
  intro henpx,
  cases henpx with x hnpx,
  have hpx : P x := hforallpx x,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intro hnenpx,
  intro x,
  by_contra hnpx,
  apply hnenpx,
  existsi x,
  assumption,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro hnforallnpx,
  by_contra hnepx,
  apply hnforallnpx,
  intro x,
  by_contra hpx,
  apply hnepx,
  existsi x,
  assumption,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  apply forall_as_neg_exists,
  apply forall_as_neg_exists_converse,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  apply exists_as_neg_forall,
  apply exists_as_neg_forall_converse,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro heand,
  cases heand with x hand,
  cases hand with hpx hqx,
  split,
  existsi x,
  assumption,
  existsi x,
  assumption,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro heor,
  cases heor with x hor,
  cases hor with hpx hqx,
  left,
  existsi x,
  assumption,
  right,
  existsi x,
  assumption,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro hor,
  cases hor with hepx heqx,
  cases hepx with x hpx,
  existsi x,
  left,
  assumption,
  cases heqx with x hqx,
  existsi x,
  right,
  assumption,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro hforalland,
  split,
  intro x,
  have hand : P x ∧ Q x := hforalland x,
  cases hand with hpx hqx,
  assumption,
  intro x,
  have hand : P x ∧ Q x := hforalland x,
  cases hand with hpx hqx,
  assumption,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro hand,
  cases hand with hforallpx hforallqx,
  intro x,
  split,
  have hpx : P x := hforallpx x,
  assumption,
  have hqx : Q x := hforallqx x,
  assumption,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intro hor,
  intro x,
  cases hor with hforallpx hforallqx,
  left,
  have hpx : P x := hforallpx x,
  assumption,
  right,
  have hqx : Q x := hforallqx x,
  assumption,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
