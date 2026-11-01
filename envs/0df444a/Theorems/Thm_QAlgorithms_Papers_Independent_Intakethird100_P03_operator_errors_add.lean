-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P03_operator_errors_add
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P03.operator_errors_add
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T03:53:40.5832+00:00
-- url     : https://prove2.me/theorems/d64bff05-e2d3-429e-83ed-71c213dae0d0
-- title:
--   Lemma 3: sum of individual operator errors
-- statement:
--   Let $U_1,\ldots,U_L$ and $\widetilde U_1,\ldots,\widetilde U_L$ be unitary operators on the same finite complex Hilbert space. Let $\delta_j\ge0$ satisfy $\|\widetilde U_j-U_j\|_{\mathrm{op}}\le\delta_j$. Then
--
--   $$
--   \|\widetilde U_L\cdots\widetilde U_1-U_L\cdots U_1\|_{\mathrm{op}}\le\sum_{j=1}^L\delta_j.
--   $$
--
--   The norm is the phase-sensitive $L_2$ operator norm. For $L=0$, both products are the identity and the bound is zero.
--
--   This keeps the source's separate precision for every gate.
-- source:
--   Quantum measurements and the Abelian Stabilizer Problem, arXiv:quant-ph/9511026v1, PDF p. 12, Lemma 3: sum of individual operator errors

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P03

noncomputable section

open scoped Matrix ComplexConjugate Kronecker

namespace QAlgorithms.Papers.Independent.Intakethird100.P03

open QAlgorithms.Papers.Independent.Renew46.P01 (cleanVector)

attribute [local instance] Classical.propDecidable

/-- PDF p.12, Lemma 3: nonuniform individual precisions add, in the phase-sensitive
L2 operator norm. The empty ordered product is the identity. -/
theorem operator_errors_add {I : Type*} [Fintype I] [DecidableEq I]
    (L : ℕ) (U V : Fin L → Matrix I I ℂ) (delta : Fin L → ℝ)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup I ℂ)
    (hV : ∀ j, V j ∈ Matrix.unitaryGroup I ℂ)
    (hd : ∀ j, 0 ≤ delta j) (happrox : ∀ j, specNorm (V j - U j) ≤ delta j) :
    specNorm (orderedProd V - orderedProd U) ≤ ∑ j, delta j := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P03

end
