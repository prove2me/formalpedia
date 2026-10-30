-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P16_exact_ppt_irreversible
-- name    : QAlgorithms.Papers.Independent.Extend50.P16.exact_ppt_irreversible
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:07:54.730789+00:00
-- url     : https://prove2.me/theorems/1c355fd0-c36a-4eee-bb76-63638a8a35e4
-- title:
--   Exact PPT manipulation has a strict distillation-cost gap
-- statement:
--   Let $\rho_v=(|v_1\rangle\langle v_1|+|v_2\rangle\langle v_2|)/2$ on two qutrits, where $|v_1\rangle=(|01\rangle-|10\rangle)/\sqrt2$ and $|v_2\rangle=(|02\rangle-|20\rangle)/\sqrt2$. Write $D_{\mathrm{PPT}}^{\mathrm{exact}}$ for the supremum of the limit-inferior yields $\log_2 d_n/n$ of sequences of positive output ranks $d_n$ and C-PPT-P channels mapping $\rho_v^{\otimes n}$ exactly and deterministically to $\Phi_{d_n}$ for every positive $n$. Then
--
--   $$
--   D_{\mathrm{PPT}}^{\mathrm{exact}}(\rho_v)\le E_N(\rho_v)<E_{\mathrm{PPT}}(\rho_v).
--   $$
--
--   This particular normalized state establishes irreversibility of exact PPT manipulation. It is not a universal claim about all entangled states.
-- source:
--   Cost of quantum entanglement simplified, arXiv:2007.14270v1, PDF p. 4, Unnumbered main result: exact PPT manipulation is irreversible

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P16

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P16

open QAlgorithms Filter

open QAlgorithms.Papers.Independent.Dependency50.P32 (partialTranspose)

open QAlgorithms.Papers.Independent.Dependency50.P41 (maximallyEntangled)

open QAlgorithms.Papers.Independent.Information100.P80 (groupedPower)

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF pp.4,22, Appendix E: exact PPT manipulation is irreversible
for this particular state; the assertion is not universal over entangled states. -/
theorem exact_ppt_irreversible :
    IsDensityMatrix rankTwoAntisymmetricState ∧
    exactDistillable rankTwoAntisymmetricState ≤ bipartiteLogNegativity rankTwoAntisymmetricState ∧
    bipartiteLogNegativity rankTwoAntisymmetricState < exactCost rankTwoAntisymmetricState := by sorry

end QAlgorithms.Papers.Independent.Extend50.P16

end
