-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P34_fourier_two_di_affine_gap
-- name    : QAlgorithms.Papers.Independent.Information100.P34.fourier_two_di_affine_gap
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:57:51.682426+00:00
-- url     : https://prove2.me/theorems/69427bdc-a4c7-4da9-9adf-5d30515e47ad
-- title:
--   Unnumbered result (C130)–(C132): DI affine-min robustness can vanish
-- statement:
--   Let $\mathcal F_2$ be the qubit Fourier channel. With multiplicative robustness and the special affine-min convention of (31),
--
--   $$R_{\max,\mathrm{DI}}(\mathcal F_2)=2\ne0=R_{\min,\mathrm{aff(DI)}}(\mathcal F_2).$$
--
--   The zero affine value is the inverse of an empty extended infimum. This counterexample prevents substituting the DI affine-min quantity for generalized robustness in Fourier distillation.
-- source:
--   The Structure of Higher-Order Quantum Resources with an Application to Coherence, arXiv:2609.40186v1, PDF p. 39, Unnumbered result (C130)–(C132)

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P34

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

namespace QAlgorithms.Papers.Independent.Information100.P34

/-- Eqs.(C130-C132), PDF pp.39-40. The affine DI value is genuinely zero
under the paper's empty-feasible-set convention. -/
theorem fourier_two_di_affine_gap :
    maxRobustness .di (fourierChannel 2) = 2 ∧
    isometricAffineMinRobustness .di (fourierChannel 2) = 0 := by sorry

end QAlgorithms.Papers.Independent.Information100.P34

end
