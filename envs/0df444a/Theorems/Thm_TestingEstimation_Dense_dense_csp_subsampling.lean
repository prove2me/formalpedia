-- Prove2me | Theorems.Thm_TestingEstimation_Dense_dense_csp_subsampling
-- name    : TestingEstimation.Dense.dense_csp_subsampling
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:14:22.420366+00:00
-- url     : https://prove2.me/theorems/b86fb543-1294-455d-9571-bf5e46d53412
-- title:
--   Theorem 3 — dense CSP subsampling with absolute quantitative constants
-- statement:
--   There are absolute constants $c_*,C_*>0$, chosen before the arity, alphabet and instance, with the following property. Let $k\ge1$, let $A$ be a finite nonempty alphabet of size $Q_0$, let $0<\theta<1$, and let $I$ be any ordered dense $k$-ary CSP on $n$ vertices with payoffs in $[0,1]$. Set
--
--   $$m=\left\lceil c_*k^{12}\theta^{-6}\log_2^2(Q_0k^2/\theta)\right\rceil.$$
--
--   If
--
--   $$n\ge c_*^2 k^{24}\theta^{-13}\log_2^4(Q_0k^2/\theta),\qquad n\ge m,$$
--
--   then, for a uniformly random $m$-subset $U$,
--
--   $$\left|\mathbb E\operatorname{Val}(U)-\operatorname{OPT}\right|\le C_*\theta.$$
--
--   Here $\operatorname{Val}(U)$ is the maximum of $|U|^{-k}$ times the sum of tuple payoffs, after choosing labels on $U$. These finite maxima are explicitly asserted to be attained. The absolute value is outside the expectation. No symmetry of the ordered predicates is assumed. This is the external sampling theorem as stated and attributed in the pinned submission; no numerical values for its two coefficients are asserted.
--
--   Differences from the source:
--   - encoding: graphs on arbitrary finite vertex sets and uniform unordered-pair or ordered-injective-tuple averages → graphs on Fin n, increasing endpoint pairs, and exact finite averages; reason: enumeration and relabeling preserve every finite instance and the source normalization
--   - encoding: minimum or maximum → real infimum or supremum together with an explicit IsLeast or IsGreatest conclusion; reason: the conclusion includes attainment and excludes a replacement by a merely unattained extremal value
--   - encoding: a dense CSP with bounded predicates and a finite label set → an ordered real table with PayoffsIn01 and a finite nonempty alphabet; reason: no tuple symmetry is added and every source instance is included
-- source:
--   Gaia Carenini, Cameron Seth, STOC 2027 submission #583 (October 2026), Theorem 3, p. 16 (PDF 16)

import Definitions.Def_TestingEstimation_Dense_CSP

noncomputable section

namespace TestingEstimation.Dense

theorem dense_csp_subsampling :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (k : ℕ), 0 < k → ∀ (A : Type) [Fintype A] [Nonempty A],
      ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ n : ℕ, ∀ I : DenseCSP n k A,
      PayoffsIn01 I →
      let Q : ℝ := Fintype.card A
      let m : ℕ := ⌈c * (k:ℝ)^12 * (θ^6)⁻¹ * (logTwo (Q*(k:ℝ)^2/θ))^2⌉₊
      c^2 * (k:ℝ)^24 * (θ^13)⁻¹ * (logTwo (Q*(k:ℝ)^2/θ))^4 ≤ (n:ℝ) →
      m ≤ n →
      |sampleValue I m - optimum I| ≤ C*θ ∧
      (∀ U : Finset (Fin n),
        IsGreatest (Set.range (cspScore I U)) (cspValue I U)) := by sorry

end TestingEstimation.Dense
