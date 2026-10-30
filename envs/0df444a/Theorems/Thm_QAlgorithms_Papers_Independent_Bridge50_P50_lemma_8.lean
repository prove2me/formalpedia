-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_lemma_8
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.lemma_8
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:27:20.150799+00:00
-- url     : https://prove2.me/theorems/1e17a600-cd1c-45f0-856a-dd89e4a6e4e1
-- title:
--   Lemma 8: lemma 8
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $S\subseteq\mathcal S$ be nonempty and closed. Write $\chi(S)$ for its divergence radius, $\sigma_*(S)$ for its selected divergence center, $\Gamma(S)$ for its peripheral states, and $\Pi(S)$ for the probability measures supported on $\Gamma(S)$ with barycenter $\sigma_*(S)$. Probability measures are Borel measures, with the weak topology. Here $\Sigma_*(S)=\arg\min_{\sigma\in\mathcal S}\sup_{\rho\in S}D(\rho\|\sigma)$ is the entire minimizer set, before uniqueness is known. Then
--   $$
--   \Sigma_*(S)\ne\varnothing,\qquad \Sigma_*(S)\text{ is convex},\qquad
--   \forall\sigma\in\Sigma_*(S)\ \forall\rho\in S:\ \ker\sigma\subseteq\ker\rho.
--   $$
--   This establishes existence and the support condition without assuming an optimizer.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 12, Lemma 8

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

/-- Lemma 8, PDF p.12: the optimizer SET is nonempty, convex and support-dominating. -/
theorem lemma_8 {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Set (Mat I)) (hS : ClosedStateSet S) :
    (centers S).Nonempty ∧ Convex ℝ (centers S) ∧
    ∀ sigma ∈ centers S, ∀ rho ∈ S, Dominates sigma rho := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
