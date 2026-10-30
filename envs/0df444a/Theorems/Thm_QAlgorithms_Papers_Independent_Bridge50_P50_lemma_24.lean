-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_lemma_24
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.lemma_24
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:37:47.288982+00:00
-- url     : https://prove2.me/theorems/a495c4e3-036a-4463-abb1-f69ae4364576
-- title:
--   Lemma 24: lemma 24
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. For each state $\rho$ and nonzero Hermitian operator $\Delta$ with $\operatorname{tr}\Delta=0$ and $\ker\rho\subseteq\ker\Delta$,
--   $$
--   \left.\frac{d^2}{d\lambda^2}H(\rho+\lambda\Delta)\right|_{\lambda=0}<0.
--   $$
--   Moreover, $H(\rho)=-\operatorname{tr}(\rho\log_2\rho)$ is strictly concave on the full density-state space. The support condition permits rank-deficient $\rho$ and ensures that the perturbation is a state for sufficiently small positive and negative $\lambda$.
--
--   This supplies both the directional curvature and its global strict-concavity consequence.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 24, Lemma 24

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

/-- Lemma 24, PDF p.24: strict negative curvature along every nonzero, traceless,
support-preserving Hermitian direction, AND strict concavity on the whole state space.
No use is made of the erroneous (1-s)^(-1) in the printed proof (114). -/
theorem lemma_24 {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] :
    (∀ rho Delta : Mat I, QAlgorithms.IsDensityMatrix rho → Delta.IsHermitian →
      Delta.trace = 0 → Delta ≠ 0 → Dominates rho Delta →
      deriv (deriv (fun t : ℝ => vnEntropy (rho + t • Delta))) 0 < 0) ∧
    StrictConcaveOn ℝ {rho : Mat I | QAlgorithms.IsDensityMatrix rho} vnEntropy := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
