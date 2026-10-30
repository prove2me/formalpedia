-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P16_appendixF_example1
-- name    : QAlgorithms.Papers.Independent.Extend50.P16.appendixF_example1
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:08:43.345297+00:00
-- url     : https://prove2.me/theorems/335c7001-91bc-45b7-84f8-b8d76e0f679f
-- title:
--   Strict kappa-negativity separation in the rank-two family
-- statement:
--   For $0<p<1$, let $\sigma_p=p|v_1\rangle\langle v_1|+(1-p)|v_2\rangle\langle v_2|$ on two qutrits, where $|v_1\rangle=(|01\rangle-|10\rangle)/\sqrt2$ and $|v_2\rangle=(|02\rangle-|20\rangle)/\sqrt2$. The operator $\sigma_p$ is a normalized state, and
--
--   $$
--   E_{\mathrm{PPT}}(\sigma_p)=E_\kappa(\sigma_p)>E_N(\sigma_p).
--   $$
--
--   The paper explicitly asserts this strict inequality throughout the open interval and supplies a numerical comparison in Figure 1. The statement retains that assertion without claiming a certified numerical error or an exact formula for kappa-entanglement.
-- source:
--   Cost of quantum entanglement simplified, arXiv:2007.14270v1, PDF p. 22, Appendix F Example 1: strict separation for rank-two family

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P16

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P16

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Information100.P80 (groupedPower)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.22, Appendix F, Example 1, (S1) and p.23, Figure 1:
the source explicitly asserts a strict gap for every 0<p<1.
The paper gives numerical evidence; no exact value for κ is inferred from the plot. -/
theorem appendixF_example1 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    IsDensityMatrix (antisymmetricFamily p) ∧
    exactCost (antisymmetricFamily p) = kappaEntanglement (antisymmetricFamily p) ∧
    bipartiteLogNegativity (antisymmetricFamily p) < kappaEntanglement (antisymmetricFamily p) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P16

end
