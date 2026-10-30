-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_lemma_12
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.lemma_12
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:29:20.358479+00:00
-- url     : https://prove2.me/theorems/86289f16-12ef-4df0-9ae0-3127f3aee6a6
-- title:
--   Lemma 12: lemma 12
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $S\subseteq\mathcal S$ be nonempty and closed. Write $\chi(S)$ for its divergence radius, $\sigma_*(S)$ for its selected divergence center, $\Gamma(S)$ for its peripheral states, and $\Pi(S)$ for the probability measures supported on $\Gamma(S)$ with barycenter $\sigma_*(S)$. Probability measures are Borel measures, with the weak topology. For the minimizer set $\Sigma_*(S)$, without any uniqueness premise,
--   $$
--   \exists!\sigma\in\mathcal S:\quad \sigma\in\Sigma_*(S).
--   $$
--   This includes existence as well as at-most-one and justifies using a selected center.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 13, Lemma 12

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

/-- Lemma 12, PDF p.13: existence and uniqueness, with neither assumed in centers. -/
theorem lemma_12 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Set (Mat I)) (hS : ClosedStateSet S) :
    ∃! sigma : Mat I, sigma ∈ centers S := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
