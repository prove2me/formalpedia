-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_lemma_3
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.lemma_3
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:24:45.507321+00:00
-- url     : https://prove2.me/theorems/470455b8-77a8-4049-9235-ef520c90f6a0
-- title:
--   Lemma 3: lemma 3
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $S\subseteq\mathcal S$ be nonempty and closed. Write $\chi(S)$ for its divergence radius, $\sigma_*(S)$ for its selected divergence center, $\Gamma(S)$ for its peripheral states, and $\Pi(S)$ for the probability measures supported on $\Gamma(S)$ with barycenter $\sigma_*(S)$. Probability measures are Borel measures, with the weak topology. Define $v_{\min}(S)$ and $v_{\max}(S)$ as the infimum and supremum over $P\in\Pi(S)$ of $\int V(\rho\|\sigma_*)\,dP(\rho)$. There are, possibly different, discrete measures $P_-,P_+\in\Pi(S)$, each supported on at most $d^2+1$ peripheral points, such that
--   $$
--   \int V(\rho\|\sigma_*)\,dP_-(\rho)=v_{\min}(S),\qquad
--   \int V(\rho\|\sigma_*)\,dP_+(\rho)=v_{\max}(S).
--   $$
--   This gives finite ensembles attaining both dispersion extrema.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 8, Lemma 3

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

/-- Lemma 3, PDF p.8: separate finite witnesses attaining the two dispersion extrema. -/
theorem lemma_3 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Set (Mat I)) (hS : ClosedStateSet S) :
    (∃ P ∈ peripheralMeasures S, FiniteSupport P ((Fintype.card I)^2+1) (peripheralStates S) ∧
      conditionalVariance P (divergenceCenter S) = vMin S) ∧
    (∃ P ∈ peripheralMeasures S, FiniteSupport P ((Fintype.card I)^2+1) (peripheralStates S) ∧
      conditionalVariance P (divergenceCenter S) = vMax S) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
