-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P05_basisHiding
-- name    : QAlgorithms.Papers.Independent.Intake100.P05.basisHiding
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:43:40.827987+00:00
-- url     : https://prove2.me/theorems/588c51a2-4701-4ba3-93e4-00b66b0b16e8
-- title:
--   Basis-independent thermal emitted ensemble
-- statement:
--   Use shot-noise units, with vacuum covariance $I$ and $[q,p]=2i$. Let $V\ge1$ be finite and let $V_a\ge0$ satisfy $V_a+1/V=V$. For $r=0$, Alice prepares the pure squeezed state of covariance $\operatorname{diag}(1/V,V)$ and mean $(a,0)$; for $r=1$ she prepares its quadrature-rotated version of mean $(0,a)$. In each case $a$ has the centered Gaussian law of variance $V_a$, independently of the basis choice. Write $\rho_{r,a}$ for these emitted densities and $\rho_{\rm th}(V)$ for the centered thermal density of quadrature variance $V$. Then
--
--   $$
--   \int \rho_{0,a}\,dG_{V_a}(a)=\rho_{\rm th}(V)=\int \rho_{1,a}\,dG_{V_a}(a).
--   $$
--
--   All prepared wavefunctions are normalized and the scalar kernel averages are integrable. The equality is of complete density kernels before the noisy channel; thus no measurement can distinguish the basis from this ensemble before its announcement. At $V=1$, $V_a=0$ and the modulation law is Dirac at zero. This is an ensemble identity, rather than a secrecy assertion about the displacement.
-- source:
--   Continuous-variable quantum key distribution protocols over noisy channels, arXiv:0806.3954v2, PDF p. 2, The protocol

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P05

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped BigOperators ENNReal

namespace QAlgorithms.Papers.Independent.Intake100.P05

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- arXiv:0806.3954v2, PDF p.2, The protocol: the Gaussian-modulated
emitted state is thermal in either basis under Va+1/V=V.
This concerns the prechannel ensemble; equality of full density kernels
precludes any basis discrimination before its public announcement. -/
theorem basisHiding (V Va : ℝ) (hV : 1 ≤ V) (hVa : 0 ≤ Va)
    (hmod : Va + 1 / V = V) :
    IsContinuousDensityKernel volume (thermalPositionKernel V) ∧
    (∀ r : Bool, averagedKernel V Va r = thermalPositionKernel V) ∧
    (∀ (r : Bool) (a : ℝ),
      Integrable (fun q => Complex.normSq (squeezedWave V r a q)) volume ∧
      (∫ q : ℝ, Complex.normSq (squeezedWave V r a q)) = 1 ∧
      IsContinuousDensityKernel volume (preparedKernel V r a)) ∧
    (∀ (r : Bool) (q t : ℝ),
      Integrable (fun a => preparedKernel V r a q t) (normalLaw Va)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P05

end
