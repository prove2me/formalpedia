-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P50_remark_5_11
-- name    : QAlgorithms.Papers.Independent.Information100.P50.remark_5_11
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T12:09:34.614225+00:00
-- url     : https://prove2.me/theorems/ce09ff71-7803-4290-b4bb-8445c9be779a
-- title:
--   Remark 5.11: The four scalar/operator perspective identities are h_H(T)=I-2 sqrt(T(I-T)); h_(H,alpha)(T)=((I-T)-T^alpha(I-T
-- statement:
--   All spaces are finite-dimensional complex Euclidean spaces. Input and output dimensions are positive wherever states or extreme eigenvalues occur. The Choi matrix $J$ is unnormalized and has output factor first. Write $\|\Theta\|_\diamond$ for the full completely bounded trace norm, $\|A\|_\infty$ for the operator norm, and $\Theta^*$ for the Hilbert–Schmidt adjoint.
--
--   For any effect $T$ and $0<\alpha<1$, let $h_f(t)=(1-t)f(t/(1-t))$ with its finite endpoint extensions. For the generators $f_H(x)=(1-\sqrt x)^2$, $f_{H,\alpha}(x)=(1-x^\alpha)/(1-\alpha)$, $f_{LC}(x)=(x-1)^2/(x+1)$, and $f_{JS}(x)=x\log x-(1+x)\log((1+x)/2)$,
--
--   $$h_H(T)=I-2\sqrt{T(I-T)},\qquad h_{H,\alpha}(T)=\frac{(I-T)-T^\alpha(I-T)^{1-\alpha}}{1-\alpha},$$
--   $$h_{LC}(T)=(2T-I)^2,\qquad h_{JS}(T)=(\log2)I+T\log T+(I-T)\log(I-T).$$
--
--   The logarithmic products use $0\log0=0$. These identities identify the scalar effect functions governing the named divergences.
-- source:
--   Quantitative upper bounds for certain quantum channel divergences, arXiv:2610.16270v1, PDF p. 21, Remark 5.11

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

/-- Remark 5.11, source PDF p.21; generators are those of Definition 5.10, PDF p.20.
The log terms use the usual 0 log 0 convention. -/
theorem remark_5_11 {r : ℕ} (T : M r) (hT : IsEffect T)
    (alpha : ℝ) (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    cfc (convexPerspective hellingerGenerator) T = 1 - (2 : ℂ) • cfc gHash T ∧
    cfc (convexPerspective (alphaGenerator alpha)) T =
      ((1 - alpha : ℝ) : ℂ)⁻¹ • ((1 - T) - cfc (hAlpha alpha) T) ∧
    cfc (convexPerspective lcGenerator) T = ((2 : ℂ) • T - 1) ^ 2 ∧
    cfc (convexPerspective jsGenerator) T =
      (Real.log 2 : ℂ) • (1 : M r) + T * cfc Real.log T + (1 - T) * cfc Real.log (1 - T) := by sorry

end QAlgorithms.Papers.Independent.Information100.P50

end
