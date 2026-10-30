-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_proposition_9
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.proposition_9
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:28:02.070818+00:00
-- url     : https://prove2.me/theorems/b7702e2b-7a79-43aa-8f54-a45ee6f4adda
-- title:
--   Proposition 9: proposition 9
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $S\subseteq\mathcal S$ be nonempty and closed. Write $\chi(S)$ for its divergence radius, $\sigma_*(S)$ for its selected divergence center, $\Gamma(S)$ for its peripheral states, and $\Pi(S)$ for the probability measures supported on $\Gamma(S)$ with barycenter $\sigma_*(S)$. Probability measures are Borel measures, with the weak topology. Let $\Sigma_*(S)$ be the entire radius-minimizer set and put $\Gamma_\sigma(S)=\arg\max_{\rho\in S}D(\rho\|\sigma)$. Then
--   $$
--   \forall\sigma\in\Sigma_*(S),\qquad \sigma\in\operatorname{conv}\Gamma_\sigma(S).
--   $$
--   This applies separately to every minimizer before uniqueness is established.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 12, Proposition 9

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

/-- Proposition 9, PDF p.12: every minimizer lies in its own peripheral convex hull. -/
theorem proposition_9 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Set (Mat I)) (hS : ClosedStateSet S) :
    ∀ sigma ∈ centers S, sigma ∈ convexHull ℝ (peripheralAt S sigma) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
