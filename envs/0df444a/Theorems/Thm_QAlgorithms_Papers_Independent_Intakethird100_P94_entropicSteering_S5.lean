-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P94_entropicSteering_S5
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P94.entropicSteering_S5
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:33:09.260817+00:00
-- url     : https://prove2.me/theorems/22fa545b-f644-4f69-a748-e6479797cbc9
-- title:
--   Entropic steering inequality for two observed marginals
-- statement:
--   Let $P(a,s,b\mid i,j)$ have a normalized local-hidden-state model with the same hidden ensemble at every pair of settings $i,j\in\{1,2\}$. Alice's binary output $a$ includes a public binary detection flag $s$, and the no-click output is predetermined. Bob's response is the Born probability of a binary rank-one projective measurement on the normalized hidden qubit state. Define $\widetilde A_i=(A_i,s_i)$ and $q=-\log_2\max_{a,b}|\langle u_{1a},u_{2b}\rangle|^2$ from Bob's two orthonormal measurement bases. Then, in bits,
--
--   $$H(B_1\mid\widetilde A_1)+H(B_2\mid\widetilde A_2)\ge q.$$
--
--   Each entropy is evaluated on its own observed same-setting marginal. Conditioning events with zero probability contribute zero. No joint distribution for incompatible Bob outcomes is required. The inequality provides a direct entropic criterion for steering.
-- source:
--   One-sided Device-Independent Quantum Key Distribution: Security, feasibility, and the connection with steering, arXiv:1109.1435v3, PDF p. 6, Eq. (S5)

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P94

noncomputable section

namespace QAlgorithms.Papers.Independent.Intakethird100.P94

open MeasureTheory

open scoped ComplexConjugate

/-- arXiv:1109.1435v3, PDF p.6, (S5): every common normalized local-hidden-state
ensemble obeys the entropic steering inequality. Neither (S3) nor (S4) is assumed. -/
theorem entropicSteering_S5 {Lambda : Type*} [MeasurableSpace Lambda]
    (U : BobBases) (L : HiddenModel Lambda U) :
    projectiveOverlapIncompatibility U ≤ flaggedConditionalEntropy L false + flaggedConditionalEntropy L true := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P94

end
