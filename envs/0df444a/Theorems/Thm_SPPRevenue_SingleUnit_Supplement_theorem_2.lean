-- Prove2me | Theorems.Thm_SPPRevenue_SingleUnit_Supplement_theorem_2
-- name    : SPPRevenue.SingleUnit.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:13:59.403365+00:00
-- url     : https://prove2.me/theorems/e8059f2d-3071-47ba-a2c9-af20f87bf672
-- title:
--   Theorem 2 (corrected: finite optimal revenue) — n-dependent SPP bounds 1/FR(n) and 1/FR-d(n,k), and Table 4
-- statement:
--   Consider a single item and $n\ge1$ buyers with independent values $v_i\sim\mu_i$. Let $t$ be a single-unit threshold mechanism (for instance the thresholds of the optimal mechanism, Lemma 1) with finite expected revenue $\mathrm{Opt}_n$. For $q_n(y)=(1-y/n)^n$, let $\mathrm{FR}(n)$ be the optimal value of
--   $$\max_{s}\int_0^\infty s(\tau)\,d\tau\ \ \text{s.t.}\ \ 0\le s(\tau)\le\min(1,1/\tau)\ (\tau\ge0),\ \ \int_0^\infty\big(1-q_n(s(\tau))\big)d\tau\le1,\ \ s\ \text{weakly decreasing},\qquad\text{(FR-n)}$$
--   and, for each integer $k\ge1$ with $s_i=i/k$, let $\mathrm{FR\text{-}d}(n,k)$ be the optimal value of the linear program
--   $$\max_{w\ge0}\sum_{i\in[k]}w_i\ \ \text{s.t.}\ \ \sum_{i=j+1}^kw_i\frac{s_j}{s_i}\le1\ (j\in[k-1]),\ \ \sum_{i=1}^kw_i\frac{1-q_n(s_i)}{s_i}\le1.\qquad\text{(FR-n-d)}$$
--
--   Then:
--
--   1. both programs attain their maximum, which is positive and finite;
--   2. there is a vector of nonnegative prices $p$ such that
--   $$\mathrm{SPP}_n(p)\ \ge\ \mathrm{Opt}_n\cdot\frac1{\mathrm{FR}(n)}\qquad\text{and}\qquad \mathrm{SPP}_n(p)\ \ge\ \mathrm{Opt}_n\cdot\frac1{\mathrm{FR\text{-}d}(n,k)}\ \text{ for every integer }k\ge1;$$
--   3. every value of Table 4 is $1/\mathrm{FR\text{-}d}(n,k)$ rounded to four decimals, for $n\in[10]$ and $k\in\{200,400,800,1600\}$.
--
--   These are the paper's bounds for a small number of buyers: they improve on Theorem 1's universal 0.6543, and the discretized programs make the factors computable.
--
--   **Formalization Note** $\mathrm{SPP}_n(p)$ is the expected revenue of the price-ordered sequential sale (published single-unit setting). One price vector serves the non-discretized bound and every $k$ at once, as in the theorem's quantifier order.
--
--   Differences from the source:
--   - generalization: Opt is the revenue of the optimal (Myerson) mechanism, for atomless or finitely supported value laws → optRev of any single-unit threshold mechanism (measurable, nonnegative, own-value independent thresholds; almost surely at most one buyer weakly above its threshold), for arbitrary value laws; reason: the proof uses only the feasible threshold benchmark. For atomless source laws, the optimal allocation and payments agree with the weak-threshold formula almost surely. For finite discrete laws, footnote 5 raises only losing-tie thresholds: allocations on the support stay the same and payments weakly increase. Thus the constructed benchmark dominates the source optimal revenue; exact payment preservation is not asserted. This does not say that every arbitrary threshold benchmark dominates Opt
--   - correction: no assumption on the optimal revenue → optRev μ t ≠ ⊤; reason: the independent atomless laws P[v₁≥x]=x^(−1/2) and P[v₂≥x]=x^(−1) for x≥1 admit the feasible truthful thresholds t₁=max(1,v₂)², t₂=√max(0,v₁)+1 with infinite revenue. Every fixed SPP or ESP has finite revenue (for ESP, E[min(v₁,v₂)]=3). DISPROOF.md checks the assumptions and calculations; the source normalization to unit revenue does not apply to this instance
--   - reading: FR(n) and FR-d(n,k) is defined as a max → the program's value is the supremum of its objective values and the statement asserts that it is attained, positive and finite (IsFactorProgram); reason: the source writes max; the formal statement proves that the max exists rather than assuming it
--   - generalization: there exists a vector of prices p → there exist prices p with p i ≥ 0 for all i; reason: a stronger conclusion: the prices found are nonnegative
--   - encoding: an n-buyer setting, [n] = {1, …, n} → 1 ≤ n, buyers Fin n (index i is buyer i + 1); reason: n ≥ 1 is the setting's standing range; q_n and r_n are undefined at n = 0
--   - encoding: 0 ≤ s(τ) ≤ min(1, 1/τ) → 0 ≤ s τ ∧ s τ ≤ 1 ∧ τ * s τ ≤ 1; reason: the same constraint at every τ ≥ 0, avoiding Lean's 1/0 = 0
--   - encoding: revenues and probabilities as real expectations → values in [0, ∞] (lower integrals and measures); the factor 1/FR as an inverse in [0, ∞]; reason: Lean convention; a revenue cannot collapse to a junk value and no instance changes
--   - reading: our approximation factors of 1/FR-d(n,k) are presented in Table 4 → each Table 4 entry d satisfies d/10⁴ − 1/(2·10⁴) ≤ 1/FR-d(n,k) < d/10⁴ + 1/(2·10⁴); reason: the table reports four decimal places. The statement retains those reports as certification obligations; floating-point primal/dual agreement in the draft is only diagnostic
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, pp. 16–17, Theorem 2, (FR-n), (FR-n-d), Table 4; proof pp. 17–18 and §8.2, pp. 31–33

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Programs

namespace SPPRevenue.SingleUnit.Supplement

open MeasureTheory
open scoped ENNReal

theorem theorem_2 :
    (∀ n : ℕ, 1 ≤ n →
      IsFactorProgram (frNValues n) ∧
      (∀ k : ℕ, 1 ≤ k → IsFactorProgram (frNdValues n k)) ∧
      ∀ (μ : Fin n → Measure ℝ), (∀ i, IsProbabilityMeasure (μ i)) →
        ∀ (t : Fin n → (Fin n → ℝ) → ℝ), IsThresholdMech μ t → optRev μ t ≠ ⊤ →
          ∃ p : Fin n → ℝ, (∀ i, 0 ≤ p i) ∧
            (frN n)⁻¹ * optRev μ t ≤ sppRev μ p ∧
            ∀ k : ℕ, 1 ≤ k → (frNd n k)⁻¹ * optRev μ t ≤ sppRev μ p) ∧
    ∀ e ∈ table4, RoundsTo4 (frNd e.1 e.2.1)⁻¹.toReal e.2.2 := by sorry

end SPPRevenue.SingleUnit.Supplement
