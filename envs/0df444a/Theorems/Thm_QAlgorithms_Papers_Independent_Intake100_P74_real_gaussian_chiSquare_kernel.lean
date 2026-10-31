-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P74_real_gaussian_chiSquare_kernel
-- name    : QAlgorithms.Papers.Independent.Intake100.P74.real_gaussian_chiSquare_kernel
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T14:59:36.086018+00:00
-- url     : https://prove2.me/theorems/e01bc3d7-0cd8-43c3-8f14-691cd24673d3
-- title:
--   Real Gaussian chi-square kernel
-- statement:
--   Let $s\ge0$ and let $X'$ have an arbitrary probability density on $\mathbb R$, with no moment assumption. Let $G$ be an independent standard normal, $Y'=\sqrt{s}X'+G$, and $Y\sim\mathcal N(0,1+s)$. For independent copies $U,V$ with the law of $X'$, define
--
--   $$
--   K_s(u,v)=\frac{1+s}{\sqrt{1+2s}}\exp\!\left[-\frac{s}{2(1+2s)}\bigl(s(u-v)^2-2uv\bigr)\right].
--   $$
--
--   Then
--
--   $$1+\chi^2(P_{Y'},P_Y)=\mathbb E[K_s(U,V)].$$
--
--   Here $\chi^2(P,Q)=\int (dP/dQ)^2\,dQ-1$, and both sides may be infinite. At $s=0$ the kernel is one. The identity turns the Gaussian output divergence into an input-law integral.
-- source:
--   Coherent-state constellations and polar codes for thermal Gaussian channels, arXiv:1603.05970v3, PDF p. 7, Appendix A, Lemma 2: real Gaussian chi-square kernel

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P74

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P74

open MeasureTheory

open scoped BigOperators ENNReal

open QAlgorithms.Papers.Independent.Dependency50.P33 (IsDensity)

open QAlgorithms.Papers.Independent.Dependency50.P39 (coherentCoefficient thermalMatrix)

open QAlgorithms.Papers.Independent.Support50.P14 (photonEnergy)

open QAlgorithms.Papers.Independent.Next46.P32 (complexNormal spectralEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P39 (thermalProbability g)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.7, Lemma 2, (16)--(18): arbitrary absolutely continuous probability
law, with no moment premise. s=0 is allowed; infinity is retained. -/
theorem real_gaussian_chiSquare_kernel
    (s : ℝ) (hs : 0 ≤ s) (mu : Measure ℝ) [IsProbabilityMeasure mu]
    (hDensity : mu ≪ volume) :
    1 + classicalChiSquare s mu =
      ∫⁻ t : ℝ × ℝ, ENNReal.ofReal (realKernel s t.1 t.2) ∂mu.prod mu := by sorry

end QAlgorithms.Papers.Independent.Intake100.P74

end
