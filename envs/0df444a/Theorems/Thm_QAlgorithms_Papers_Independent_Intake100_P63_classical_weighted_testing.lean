-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P63_classical_weighted_testing
-- name    : QAlgorithms.Papers.Independent.Intake100.P63.classical_weighted_testing
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:27:49.349739+00:00
-- url     : https://prove2.me/theorems/5eaed5c5-561e-461f-bcec-eebb1b1ff7b8
-- title:
--   Lemma C.7: classical weighted testing bound (adapted from Han)
-- statement:
--   Let p and q be probability distributions on the same finite nonempty alphabet X, let $0\le\lambda_i\le1$ for every $i\in X$, and let $\mu\in\mathbb R$. Then
--   $$
--   \sum_{i\in X}\lambda_i\bigl(p_i-2^\mu q_i\bigr)
--   \le\sum_{\{i:p_i\ge2^\mu q_i\}}p_i.
--   $$
--
--   This is the source proof’s support-safe version of the event $\log_2(p_i/q_i)\ge\mu$: p_i=q_i=0 contributes zero weight, and p_i>0=q_i is included.
-- source:
--   A Generalization of Quantum Stein's Lemma, arXiv:0904.0281v3, PDF p. 34, Lemma C.7: classical weighted testing bound (adapted from Han)

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P63

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P63

open QAlgorithms Filter Topology

open QAlgorithms.Papers.Independent.Information100.P60 (Mat relativeBits)

open QAlgorithms.Papers.Independent.Information100.P07 (positivePart)

open QAlgorithms.Papers.Independent.Information100.P21 (Vec)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

open QAlgorithms.Papers.Independent.Advance50.P30 (joinCopies defectTensor)

open QAlgorithms.Papers.Independent.Information100.P69 (permute)

open scoped Matrix ComplexConjugate ENNReal ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.34 Lemma C.7 Eqs.(C16),(C17): the event p_i≥2^mu q_i is the
source proof's support-safe interpretation of log(p_i/q_i)≥mu. -/
theorem classical_weighted_testing {K : Type*} [Fintype K] [Nonempty K]
    (p q weight : K → ℝ) (hp : (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1)
    (hq : (∀ i, 0 ≤ q i) ∧ (∑ i, q i) = 1)
    (hweight : ∀ i, weight i ∈ Set.Icc (0 : ℝ) 1) (mu : ℝ) :
    (∑ i, weight i * (p i - (2 : ℝ) ^ mu * q i)) ≤
      ∑ i, if (2 : ℝ) ^ mu * q i ≤ p i then p i else 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P63

end
