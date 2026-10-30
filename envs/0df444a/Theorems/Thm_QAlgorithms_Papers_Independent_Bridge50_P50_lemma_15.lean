-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_lemma_15
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.lemma_15
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:31:37.826311+00:00
-- url     : https://prove2.me/theorems/688efd16-91e4-4c03-af54-3bdd5a3d4cac
-- title:
--   Lemma 15: lemma 15
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $S\subseteq\mathcal S$ be nonempty and closed. Write $\chi(S)$ for its divergence radius, $\sigma_*(S)$ for its selected divergence center, $\Gamma(S)$ for its peripheral states, and $\Pi(S)$ for the probability measures supported on $\Gamma(S)$ with barycenter $\sigma_*(S)$. Probability measures are Borel measures, with the weak topology. Let $P$ be a finite probability mass function in $\Pi(S)$ and let $\bar\rho_P=\sum_\rho P(\rho)\rho$. Define the block states $\omega_P=\bigoplus_\rho P(\rho)\rho$ and $\zeta_P=\bigoplus_\rho P(\rho)\bar\rho_P$. Then
--   $$
--   \sum_\rho P(\rho)V(\rho\|\bar\rho_P)=V(\omega_P\|\zeta_P).
--   $$
--   Zero weights are allowed. The barycenter and peripheral conditions remove the extra classical variance term.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 16, Lemma 15

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

/-- Lemma 15, PDF pp.16,30: Pi membership removes the classical between-block variance. -/
theorem lemma_15 {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Set (Mat I)) (hS : ClosedStateSet S) (E : Ensemble I)
    (hE : PeripheralEnsemble S E) :
    ensembleVariance E = pairInformationVariance (cqJointState E) (referenceState E) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
