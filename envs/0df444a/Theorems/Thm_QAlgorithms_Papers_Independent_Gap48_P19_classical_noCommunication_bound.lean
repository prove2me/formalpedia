-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P19_classical_noCommunication_bound
-- name    : QAlgorithms.Papers.Independent.Gap48.P19.classical_noCommunication_bound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-22T04:11:42.444719+00:00
-- url     : https://prove2.me/theorems/353969c5-7aa4-45d7-a639-d1fab48841fa
-- title:
--   Classical distillation bound without communication
-- statement:
--   Let $p_{AB}$ and $q_{A'B'}$ be independent finite input laws, with equal unprimed and primed local alphabets, all nonempty. Alice applies a stochastic map $AA'\to aa'$ and Bob applies a stochastic map $BB'\to bb'$, with no communication. Retain only protocols for which the computed probability of $a'=a_0,b'=b_0$ is positive. Define $E_F$ by the attained CMI minimum over all positive finite auxiliary cardinalities, and $E_D$ by the attained maximum over these local protocols of the analogous minimum for the selected output law. Then these extrema exist and
--
--   $$E_D(p,q)\le E_F(p)+E_F(q),\qquad E_D(p,q)=E_F(p)=E_F(q)=0.$$
--
--   The equalities record the degeneracy of the unrestricted classical auxiliary convention. No general postselection data-processing statement is asserted.
-- source:
--   Entanglement of Distillation and Conditional Mutual Information, arXiv:quant-ph/0202144v2, PDF p. 6, §3, Eq.(15)

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P19

namespace QAlgorithms.Papers.Independent.Gap48.P19

open scoped ComplexConjugate Matrix

open QAlgorithms.Papers.Independent.Information100.P75 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.6, (15): no-communication classical ED bound, with attained extrema.
Unrestricted finite auxiliaries make all three quantities zero. Every finite input law admits
(12) via a flag copying AB. The erroneous temporal-independence step (19) is not assumed. -/
theorem classical_noCommunication_bound {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (p q : A × B → ℝ)
    (hp : IsLaw p) (hq : IsLaw q) (a0 : A) (b0 : B) :
    ∃ ed ef efprime : ℝ,
      IsGreatest (classicalDistillationScores p q a0 b0) ed ∧
      IsLeast (classicalScores p) ef ∧ IsLeast (classicalScores q) efprime ∧
      ed ≤ ef + efprime ∧ ed = 0 ∧ ef = 0 ∧ efprime = 0 ∧
      (∀ k : ClassicalProtocol A B, 0 < localSelectionProbability p q k a0 b0 →
        IsLeast (classicalScores (classicalOutput p q k a0 b0)) 0) := by sorry

end

end QAlgorithms.Papers.Independent.Gap48.P19
