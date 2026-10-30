-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_direct_theorem_4
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.direct_theorem_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:40:34.230011+00:00
-- url     : https://prove2.me/theorems/2c28a0a6-8858-4710-9503-acb23eb95a43
-- title:
--   Direct Theorem 4: direct theorem 4
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $W:X\to\mathcal S$ be a channel from an arbitrary nonempty set, with no countability or topology assumption on $X$, and fix $0<\varepsilon<1$. Let $M^*(W^n,\varepsilon)$ optimize finite nonempty uniform-message codes with average decoding error at most $\varepsilon$ and an arbitrary collective POVM. Put $S=\overline{\operatorname{im}W}$, $v_\varepsilon(S)=v_{\min}(S)$ for $\varepsilon\le1/2$ and $v_{\max}(S)$ otherwise, and let $\Phi^{-1}$ be the standard normal quantile. There exist fixed $C>0,N\ge2$ such that
--   $$
--   \log_2 M^*(W^n,\varepsilon)\ge n\chi(S)+\sqrt{n v_\varepsilon(S)}\Phi^{-1}(\varepsilon)-C\log_2 n\qquad(n\ge N).
--   $$
--   This is the stronger direct bound, valid even when $v_\varepsilon(S)=0$ and without finite input alphabet assumptions.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 15, Direct Theorem 4

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

/-- Direct Part of Theorem 4, PDF pp.15–16, (55): eventual logarithmic lower remainder
for every channel, including zero dispersion. -/
theorem direct_theorem_4 {X I : Type*} [Nonempty X] [Fintype I] [DecidableEq I] [Nonempty I]
    (W : X → Mat I) (hW : ∀ x, QAlgorithms.IsDensityMatrix (W x))
    (e : ℝ) (he : 0 < e ∧ e < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
      secondOrder (closure (Set.range W)) e n - C * logTwo n ≤ blockLog W e n := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
