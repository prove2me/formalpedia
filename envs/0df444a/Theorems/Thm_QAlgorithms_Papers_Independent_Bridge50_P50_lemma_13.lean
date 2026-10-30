-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_lemma_13
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.lemma_13
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:30:08.536688+00:00
-- url     : https://prove2.me/theorems/da3d4749-7b95-4c47-baf8-13eb339b938d
-- title:
--   Lemma 13: lemma 13
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $S\subseteq\mathcal S$ be nonempty and closed. Write $\chi(S)$ for its divergence radius, $\sigma_*(S)$ for its selected divergence center, $\Gamma(S)$ for its peripheral states, and $\Pi(S)$ for the probability measures supported on $\Gamma(S)$ with barycenter $\sigma_*(S)$. Probability measures are Borel measures, with the weak topology. With $\bar\rho_P=\int\rho\,dP(\rho)$ and $I(P)=\int D(\rho\|\bar\rho_P)\,dP(\rho)$,
--   $$
--   \chi(S)=\sup_{P\in\mathcal P(S)}I(P).
--   $$
--   There is a maximizing discrete measure supported on at most $d^2$ points in $\Gamma(S)$. This provides attained finite dual optimization, beyond the equality of values.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 14, Lemma 13

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P50

noncomputable section

open scoped Topology BigOperators ComplexConjugate ComplexOrder ENNReal Matrix.Norms.L2Operator

open MeasureTheory Filter Set

namespace QAlgorithms.Papers.Independent.Bridge50.P50

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted primitives; these names do not create local declarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat logTwo testingBeta normalCDF normalQuantile)

open QAlgorithms.Papers.Independent.Information100.P08 (Ensemble ensembleAverage)

open QAlgorithms.Papers.Independent.Information100.P69 (entropy)

open QAlgorithms.Papers.Independent.Dependency50.P35 (Dominates)

open QAlgorithms.Papers.Independent.Dependency50.P36 (pairInformationVariance)

open QAlgorithms (vnEntropy traceDistance minEigenvalue)

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelMeasurable

attribute [local instance] QAlgorithms.Papers.Independent.Bridge50.P50.matrixBorelSpace

/-- Lemma 13, PDF p.14: dual formula and finite attainment with at most d^2 peripheral points. -/
theorem lemma_13 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Set (Mat I)) (hS : ClosedStateSet S) :
    divergenceRadius S = (⨆ P : {P : ProbabilityMeasure (Mat I) // P ∈ measuresOn S}, borelHolevoInformation P.val) ∧
    ∃ P ∈ measuresOn S, borelHolevoInformation P = divergenceRadius S ∧
      FiniteSupport P ((Fintype.card I)^2) (peripheralStates S) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
