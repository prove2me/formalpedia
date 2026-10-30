-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P50_theorem_4
-- name    : QAlgorithms.Papers.Independent.Bridge50.P50.theorem_4
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T09:25:35.740471+00:00
-- url     : https://prove2.me/theorems/53dcbdc3-940b-42fa-abef-424ee2b770ba
-- title:
--   Theorem 4: Second-order c-q coding asymptotics
-- statement:
--   Let $\mathcal S$ be the density operators on a nonzero, finite-dimensional complex Hilbert space of dimension $d$. Logarithms are in bits, $D$ is support-aware Umegaki relative entropy, and $V$ is relative entropy variance in bits squared. Let $W:X\to\mathcal S$ be a channel from an arbitrary nonempty set, with no countability or topology assumption on $X$, and fix $0<\varepsilon<1$. Let $M^*(W^n,\varepsilon)$ optimize finite nonempty uniform-message codes with average decoding error at most $\varepsilon$ and an arbitrary collective POVM. Put $S=\overline{\operatorname{im}W}$, $v_\varepsilon(S)=v_{\min}(S)$ for $\varepsilon\le1/2$ and $v_{\max}(S)$ otherwise, and let $\Phi^{-1}$ be the standard normal quantile. The operational classical capacity equals $C(W)=\chi(S)$. With the actual difference $K_n$ as remainder,
--   $$
--   \log_2 M^*(W^n,\varepsilon)=n\chi(S)+\sqrt{n v_\varepsilon(S)}\,\Phi^{-1}(\varepsilon)+K_n,\qquad
--   \frac{K_n}{\sqrt n}\longrightarrow0.
--   $$
--   If $S$ is finite and $v_\varepsilon(S)>0$, there exist fixed $C>0$ and $N\ge2$ such that $|K_n|\le C\log_2 n$ for every $n\ge N$.
--
--   This is the complete second-order formula, including the stronger finite-image remainder.
-- source:
--   Second-Order Asymptotics for the Classical Capacity of Image-Additive Quantum Channels, arXiv:1308.6503v3, PDF p. 8, Theorem 4

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

/-- Theorem 4, PDF p.8, (24)–(25): arbitrary nonempty input alphabet, closure of the
image, sqrt(n V), the minimum branch at 1/2, and both remainder regimes. -/
theorem theorem_4 {X I : Type*} [Nonempty X] [Fintype I] [DecidableEq I] [Nonempty I]
    (W : X → Mat I) (hW : ∀ x, QAlgorithms.IsDensityMatrix (W x))
    (e : ℝ) (he : 0 < e ∧ e < 1) :
    cqOperationalCapacity W = capacityBits (closure (Set.range W)) ∧
    (∀ n : ℕ, 1 ≤ n → blockLog W e n =
      secondOrder (closure (Set.range W)) e n + cqRemainder W e n) ∧
    Tendsto (fun n : ℕ => cqRemainder W e n / Real.sqrt n) atTop (𝓝 0) ∧
    ((closure (Set.range W)).Finite → 0 < vEpsilon (closure (Set.range W)) e →
      ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n →
        |cqRemainder W e n| ≤ C * logTwo n) := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P50

end
