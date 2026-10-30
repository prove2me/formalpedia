-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P37_sphereSampling
-- name    : QAlgorithms.Papers.Independent.Advance50.P37.sphereSampling
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T08:38:46.714985+00:00
-- url     : https://prove2.me/theorems/40d277e2-f2ed-469b-bd73-3a7ec50cb6a1
-- title:
--   Uniform spherical modulation by Gaussian normalization
-- statement:
--   Let $\alpha>0$, let $G\in\mathbb R^8$ have eight independent standard normal coordinates, and let $\mu_\alpha$ be seven-dimensional Hausdorff measure restricted to the Euclidean sphere $S^7(2\alpha)$ and divided by its total surface measure. That surface measure is positive and finite. Define $R_\alpha(g)=2\alpha g/\|g\|$ for $g\ne0$ and $R_\alpha(0)=(2\alpha,0,\ldots,0)$. This map is measurable and
--
--   $$
--   \mathcal L(R_\alpha(G))=\mu_\alpha.
--   $$
--
--   Pair successive real coordinates as $z_j=x_{2j}+i x_{2j+1}$, $j=0,1,2,3$. Every normalized vector, including the specified zero-input fallback, satisfies $\sum_{j=0}^3|z_j|^2=4\alpha^2$; the same identity holds $\mu_\alpha$-almost everywhere. Thus this procedure samples exactly the coherent-amplitude ensemble in Eq. (2).
--
--   The independence, common variance and centering make the Gaussian isotropic; these are the intended assumptions of footnote 4.
-- source:
--   Long distance quantum key distribution with continuous variables, arXiv:1005.0328v3, PDF p. 5, Section 2, Eq. (2) and footnote 4: normalized Gaussian sampling of the uniform sphere modulation

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P37

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Advance50.P37

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Gap48.P26 (totalPhotons)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (IsDensity IsBarycenter IsTraceClassChannel productCoeff)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (FockIndex DensityKernel Cov standardFormCovariance vacuumKernel productWeyl weylArgument)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel boundedUnitaryConjugation partialRight)

open QAlgorithms.Papers.Independent.Support50.P14 (CompleteMoments GaussianAt)

open QAlgorithms.Papers.Independent.Renew46.P39 (squeezedVacuum)

open QAlgorithms.Papers.Independent.Renew46.P41
  (coherentProductCoefficient NormalizedCoherent)

/-- PDF pp.4--5, Eq.(2), footnote 4: normalizing independent isotropic
Gaussians gives the independently defined uniform surface probability.
Positivity/finiteness guard the Hausdorff normalization. -/
theorem sphereSampling (alpha : ℝ) (halpha : 0 < alpha) :
    0 < (Measure.hausdorffMeasure 7 : Measure ModulationSpace)
      (Metric.sphere 0 (2 * alpha)) ∧
    (Measure.hausdorffMeasure 7 : Measure ModulationSpace)
      (Metric.sphere 0 (2 * alpha)) < ⊤ ∧
    IsProbabilityMeasure (sphericalModulation alpha) ∧
    Measurable (normalizeModulation alpha) ∧
    Measure.map (normalizeModulation alpha) standardModulationGaussian =
      sphericalModulation alpha ∧
    (∀ x, ∑ j : Fin 4, Complex.normSq
      (modulationAmplitudes (normalizeModulation alpha x) j) = 4 * alpha ^ 2) ∧
    (∀ᵐ x ∂sphericalModulation alpha,
      ∑ j : Fin 4, Complex.normSq (modulationAmplitudes x j) = 4 * alpha ^ 2) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P37

end
