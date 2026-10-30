-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_lemma_27
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.lemma_27
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-29T09:38:33.891028+00:00
-- url     : https://prove2.me/theorems/68b30249-cd0d-48bb-93fb-22450f61a472
-- title:
--   Lemma 27: lemma 27
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. For any subset $S\subseteq\mathcal S$ and $\lambda_0>0$, there is a finite real constant $V^+$ such that
--   $$
--   \forall\rho\in S\ \forall\sigma\in\mathcal S:\quad
--   \lambda_{\min}(\sigma)\ge\lambda_0\ \Longrightarrow\ V(\rho\|\sigma)\le V^+.
--   $$
--   No closedness is required of $S$. The bound is uniform in both states; if the comparison-state domain is empty the universal conclusion is vacuous, as in the source.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 27, Lemma 27

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

/-- Lemma 27, PDF p.27: uniform in rho AND all sigma with the given positive eigenvalue
lower bound. S need not be closed. Empty feasible comparison sets are harmless. -/
theorem lemma_27 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (S : Set (Mat I)) (hS : ∀ rho ∈ S, QAlgorithms.IsDensityMatrix rho)
    (l0 : ℝ) (hl0 : 0 < l0) :
    ∃ V : ℝ, ∀ rho ∈ S, ∀ sigma : Mat I, QAlgorithms.IsDensityMatrix sigma →
      l0 ≤ minEigenvalue sigma → pairInformationVariance rho sigma ≤ V := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
