-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_classicalSSA
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.classicalSSA
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:47:29.084069+00:00
-- url     : https://prove2.me/theorems/a4822e8c-63f9-4f94-a560-dba62b915c3e
-- title:
--   Section 2.1: classical SSA equality and Markov condition
-- statement:
--   Let $p(a,b,c)>0$ be a probability mass function on finite nonempty alphabets, with marginals $p_{AB},p_{BC},p_B$. Write $H$ for Shannon entropy in nats. Then
--   $$H(p_{ABC})+H(p_B)\le H(p_{AB})+H(p_{BC}).$$
--   Equality is equivalent to each of the following identities holding for every $a,b,c$:
--   $$p(a,b,c)=\frac{p_{AB}(a,b)p_{BC}(b,c)}{p_B(b)},$$
--   $$\log p(a,b,c)-\log p_{AB}(a,b)=\log p_{BC}(b,c)-\log p_B(b),$$
--   $$\frac{p(a,b,c)}{p_{AB}(a,b)}=\frac{p_{BC}(b,c)}{p_B(b)}.$$
--   The last identity is the Markov condition $p(c\mid a,b)=p(c\mid b)$. All marginals and conditional probabilities are computed from the joint law.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 6, Section 2.1: classical SSA equality and Markov condition

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P51

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakethird100.P51

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact interfaces from the frozen accepted library; no local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy marginalAB channelAdjoint)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAC)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Gap48.P33 (measurementInformation)

section Statements

variable {A B C D J K O : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype J] [Fintype K] [Fintype O]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq J] [DecidableEq K] [DecidableEq O]

/-- Section 2.1, equations (9)–(12), PDF p.6: classical SSA and all three equivalent
Markov equality forms. Marginals and conditional probabilities are computed from p. -/
theorem classicalSSA [Nonempty A] [Nonempty B] [Nonempty C] (p : A × (B × C) → ℝ) (hp : ∀ x, 0 < p x) (hs : ∑ x, p x = 1) :
    let ab := fun a b => ∑ c, p (a, (b, c))
    let bc := fun b c => ∑ a, p (a, (b, c))
    let pb := fun b => ∑ a, ∑ c, p (a, (b, c))
    let gap := shannonNats (fun x : A × B => ab x.1 x.2) +
      shannonNats (fun x : B × C => bc x.1 x.2) - shannonNats p - shannonNats pb
    0 ≤ gap ∧
    (gap = 0 ↔ ∀ a b c, p (a, (b, c)) = ab a b * bc b c / pb b) ∧
    (gap = 0 ↔ ∀ a b c, Real.log (p (a, (b, c))) - Real.log (ab a b) =
      Real.log (bc b c) - Real.log (pb b)) ∧
    (gap = 0 ↔ ∀ a b c, p (a, (b, c)) / ab a b = bc b c / pb b) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
