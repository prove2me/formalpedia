-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P89_tmssEntanglementComparison
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P89.tmssEntanglementComparison
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T04:24:11.037572+00:00
-- url     : https://prove2.me/theorems/d251cc5e-435d-4df1-9b50-32a6e77b28a8
-- title:
--   Strict fixed-entanglement advantage over pure TMSS teleportation
-- statement:
--   Let $\lambda>0$ and $r\ge0$ be finite. Let $\overline F_{\rm opt}(\lambda,r)$ be the closed-region Gaussian optimum, equal to the finite-energy BK fidelity supremum, and let $\overline F_{\rm TMSS}(\lambda,r)$ be the independently defined optimized-gain fidelity for a fixed pure TMSS of logarithmic negativity $2r$. Then
--
--   $$\overline F_{\rm opt}(\lambda,r)\ge\overline F_{\rm TMSS}(\lambda,r)\ge\overline F_{\rm opt}(\lambda,0).$$
--
--   Each equality holds if and only if $r=0$. Both inequalities are strict for $r>0$. For each fixed $r\ge0$,
--
--   $$\lim_{\lambda\to0^+}\left[\overline F_{\rm opt}(\lambda,r)-\overline F_{\rm TMSS}(\lambda,r)\right]=0.$$
--
--   The advantage concerns shared logarithmic negativity, with no simultaneous fixed-energy constraint. In the first branch of (13), the larger optimum is a limiting supremum rather than a finite-energy attainable value. The broad-prior saturation is a limit of normalized ensembles.
-- source:
--   Optimal continuous variable quantum teleportation with limited resources, arXiv:1705.03017v5, PDF p. 4, Strict resource-entanglement advantage over TMSS teleportation

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P89

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P89

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClassChannel tensorApply traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P39
  (coherentKet coherentCoefficient operatorOfMatrix husimiQ HasFockMatrix CoherentRealized)

open QAlgorithms.Papers.Independent.Frontier30.P14 (weylCharacteristic)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov FockIndex DensityKernel PhysicalCovariance CharacteristicSummable
   multimodeWeylTrace covarianceCharacteristicValue standardFormCovariance)

open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)

open QAlgorithms.Papers.Independent.Gap48.P26 (PhaseInsensitive coherentKernel)

open QAlgorithms.Entanglement (partialTransposeFirst)

/-- PDF p.4, after (16): strict entanglement advantage at finite nonzero prior
width and r>0; both equality cases are r=0. The first gap vanishes as lambda->0+.
This compares fixed entanglement, without asserting equal resource energies. -/
theorem tmssEntanglementComparison (lambda r : ℝ) (hlambda : 0 < lambda) (hr : 0 ≤ r) :
    tmssOptimum lambda r ≤ scalarOptimum lambda r ∧
    scalarOptimum lambda 0 ≤ tmssOptimum lambda r ∧
    (scalarOptimum lambda r = tmssOptimum lambda r ↔ r = 0) ∧
    (tmssOptimum lambda r = scalarOptimum lambda 0 ↔ r = 0) ∧
    (0 < r → tmssOptimum lambda r < scalarOptimum lambda r ∧
      scalarOptimum lambda 0 < tmssOptimum lambda r) ∧
    Tendsto (fun ell => scalarOptimum ell r - tmssOptimum ell r)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P89

end
