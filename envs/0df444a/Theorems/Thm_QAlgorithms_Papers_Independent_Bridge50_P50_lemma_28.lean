-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_lemma_28
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.lemma_28
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:39:09.481008+00:00
-- url     : https://prove2.me/theorems/50fc35e9-d5fe-4f37-b07a-7da8831de05c
-- title:
--   Lemma 28: lemma 28
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $S\subseteq\mathcal S$ be arbitrary and fix a state $\sigma$ with $\lambda_{\min}(\sigma)>0$. Let $T(\rho\|\sigma)$ be the centered absolute third moment of the log-likelihood ratio of the Nussbaum–Szkoła distributions. There is a finite real constant $T^+$ such that
--   $$
--   \forall\rho\in S:\quad T(\rho\|\sigma)\le T^+.
--   $$
--   This is a bound on a classical spectral-law moment, not a noncommutative absolute cube, and requires no closedness of $S$.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 28, Lemma 28

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

/-- Lemma 28, PDF p.28: fixed full-rank sigma, no closedness assumption on S. -/
theorem lemma_28 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Set (Mat I)) (hS : ∀ rho ∈ S, QAlgorithms.IsDensityMatrix rho)
    (sigma : Mat I) (hsigma : QAlgorithms.IsDensityMatrix sigma) (hpos : 0 < minEigenvalue sigma) :
    ∃ T : ℝ, ∀ rho ∈ S, thirdMoment rho sigma ≤ T := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
