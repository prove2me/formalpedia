-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P23_kms_iff_gibbs
-- name    : QAlgorithms.Papers.Independent.Next46.P23.kms_iff_gibbs
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:41:17.834725+00:00
-- url     : https://prove2.me/theorems/8aff45c3-c171-4407-bb36-b3e5f2784908
-- title:
--   Proposition 2.20
-- statement:
--   Let $H=H^*$ and let $\rho$ be a normalized state on a nonzero finite-dimensional complex Hilbert space. For every real inverse temperature $\beta$, $$\rho(AB)=\rho(\tau^{-i\beta}(B)A)\ \text{for all }A,B\quad\Longleftrightarrow\quad \rho=\frac{e^{-\beta H}}{\operatorname{tr}(e^{-\beta H})}.$$ Complex-time dynamics has its entire exponential definition. No positivity condition on $\beta$ is added.
-- source:
--   Entropic Fluctuations in Quantum Statistical Mechanics. An Introduction, arXiv:1106.3786v1, PDF p. 53, Proposition 2.20

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P23

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator Topology

namespace QAlgorithms.Papers.Independent.Next46.P23

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P15 (propagator legendre rightSlope leftSlope FiniteExperiment exponentialMoment)

open QAlgorithms.Papers.Independent.Dependency50.P05 (uniformDensity)

open QAlgorithms.Papers.Independent.Dependency50.P28 (Schwarz)

open QAlgorithms.Papers.Independent.Frontier30.P28 (inverseExponent)

open QAlgorithms.Papers.Independent.Information100.P07 (support)

open QAlgorithms.Papers.Independent.Information100.P50 (schattenNorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (Mat)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

open QAlgorithms (traceRight)

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- Proposition2.20, KMS iff Gibbs, no positivity condition on beta; source PDF p.53. -/
theorem kms_iff_gibbs [Nonempty I] (H rho : Mat I) (hH : H.IsHermitian)
    (hrho : QAlgorithms.IsDensityMatrix rho) (beta : ℝ) :
    KMS H rho beta ↔ rho = QAlgorithms.gibbsState ((-(beta : ℂ)) • H) := by sorry

end QAlgorithms.Papers.Independent.Next46.P23

end
