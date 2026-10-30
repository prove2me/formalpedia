-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_theorem_2
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.theorem_2
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:24:11.335974+00:00
-- url     : https://prove2.me/theorems/363c133d-9465-4fe8-998c-4a09a9fba904
-- title:
--   Theorem 2: Divergence-center geometry and all maximizing measures
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $S\subseteq\mathcal S$ be nonempty and closed. Write $\chi(S)$ for its divergence radius, $\sigma_*(S)$ for its selected divergence center, $\Gamma(S)$ for its peripheral states, and $\Pi(S)$ for the probability measures supported on $\Gamma(S)$ with barycenter $\sigma_*(S)$. Probability measures are Borel measures, with the weak topology.
--
--   The radius minimizer exists uniquely, its support contains every state in $S$, and
--   $$
--   D(\rho\|\sigma_*)\le\chi(S),\quad
--   D(\rho\|\sigma_*)=\chi(S)\iff\rho\in\Gamma(S),\quad
--   \sigma_*\in\operatorname{conv}\Gamma(S).
--   $$
--   For a Borel probability measure $P$ on $S$, let $\bar\rho_P=\int\rho\,dP(\rho)$ and $I(P)=\int D(\rho\|\bar\rho_P)\,dP(\rho)$. Then
--   $$
--   \chi(S)=\sup_{P\in\mathcal P(S)} I(P),\qquad
--   \{P\in\mathcal P(S):I(P)=\chi(S)\}=\Pi(S).
--   $$
--   The set $\Pi(S)$ is compact and convex and contains a discrete measure supported on at most $d^2$ peripheral states.
--
--   This identifies both the radius and all maximizing ensembles from output-space geometry.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 6, Theorem 2

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

/-- Theorem 2, PDF pp.6–7: all five assertions, including optimizer characterization,
weak compactness, convexity and the d^2 support bound. -/
theorem theorem_2 {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Set (Mat I)) (hS : ClosedStateSet S) :
    (∃! sigma : Mat I, sigma ∈ centers S) ∧
    divergenceCenter S ∈ centers S ∧ (∀ rho ∈ S, Dominates (divergenceCenter S) rho) ∧
    (∀ rho ∈ S, entropy rho (divergenceCenter S) ≤ divergenceRadius S ∧
      (entropy rho (divergenceCenter S) = divergenceRadius S ↔ rho ∈ peripheralStates S)) ∧
    divergenceCenter S ∈ convexHull ℝ (peripheralStates S) ∧
    divergenceRadius S = (⨆ P : {P : ProbabilityMeasure (Mat I) // P ∈ measuresOn S}, borelHolevoInformation P.val) ∧
    (∀ P ∈ measuresOn S, borelHolevoInformation P = divergenceRadius S ↔ P ∈ peripheralMeasures S) ∧
    IsCompact (peripheralMeasures S) ∧ MeasureConvex (peripheralMeasures S) ∧
    (∃ P ∈ peripheralMeasures S, FiniteSupport P ((Fintype.card I)^2) (peripheralStates S)) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
