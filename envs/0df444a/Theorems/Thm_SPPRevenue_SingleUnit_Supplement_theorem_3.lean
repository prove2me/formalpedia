-- Prove2me | Theorems.Thm_SPPRevenue_SingleUnit_Supplement_theorem_3
-- name    : SPPRevenue.SingleUnit.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T20:16:39.443859+00:00
-- url     : https://prove2.me/theorems/7db330ff-fd8b-44a9-a03f-700782b51da8
-- title:
--   Theorem 3 (corrected: finite optimal revenue) — H-unit SPP earns Opt_H/FR-Multi(H), and 1/FR-Multi(H) > 1 − H^H/(H!e^H)
-- statement:
--   Let $H\ge1$ and $f_H(x)=H-e^{-x}\sum_{i=0}^{H-1}(H-i)x^i/i!$, and let $\mathrm{FR\text{-}Multi}(H)$ be the optimal value of
--   $$\max_s\int_0^\infty s(\tau)\,d\tau\ \ \text{s.t.}\ \ 0\le s(\tau)\le\min(H,1/\tau)\ (\tau\ge0),\ \ \int_0^\infty f_H(s(\tau))\,d\tau\le1,\ \ s\ \text{weakly decreasing}.$$
--   Then:
--
--   1. the program attains its maximum, which is positive and finite;
--   2. the factor beats the previous best bound:
--   $$\frac1{\mathrm{FR\text{-}Multi}(H)}\ >\ 1-\frac{H^H}{H!\,e^H};$$
--   3. for every $n\ge1$, independent values $v_i\sim\mu_i$ and every $H$-unit threshold mechanism (for instance the optimal one) with finite expected revenue $\mathrm{Opt}_H$, there are nonnegative prices $p$ with
--   $$\mathrm{SPP}_H(p)\ \ge\ \mathrm{Opt}_H\cdot\frac1{\mathrm{FR\text{-}Multi}(H)}.$$
--
--   For $H=1$ the program is (FR) and the factor is that of Theorem 1.
--
--   **Formalization Note** $\mathrm{SPP}_H(p)$ is the expected revenue of the price-ordered sale of $H$ units. The improvement in item 2 is stated as an inequality in $[0,\infty]$ between $\max(0,1-H^H/(H!e^H))$ and the inverse of the program's value.
--
--   Differences from the source:
--   - generalization: Opt_H is the revenue of the optimal H-unit mechanism, for atomless or finitely supported laws → optRev of any H-unit threshold mechanism (almost surely at most H buyers above their thresholds), for arbitrary value laws; reason: the proof uses only the feasible threshold benchmark. For atomless source laws, the optimal allocation and payments agree with the weak-threshold formula almost surely. For finite discrete laws, footnote 5 raises only losing-tie thresholds: allocations on the support stay the same and payments weakly increase. Thus the constructed benchmark dominates the source optimal revenue; exact payment preservation is not asserted. This does not say that every arbitrary threshold benchmark dominates Opt
--   - correction: no assumption on the optimal revenue → optRev μ t ≠ ⊤; reason: the independent atomless laws P[v₁≥x]=x^(−1/2) and P[v₂≥x]=x^(−1) for x≥1 admit the feasible truthful thresholds t₁=max(1,v₂)², t₂=√max(0,v₁)+1 with infinite revenue. Every fixed SPP or ESP has finite revenue (for ESP, E[min(v₁,v₂)]=3). DISPROOF.md checks the assumptions and calculations; the source normalization to unit revenue does not apply to this instance
--   - reading: FR-Multi(H) is defined as a max → the program's value is the supremum of its objective values and the statement asserts that it is attained, positive and finite (IsFactorProgram); reason: the source writes max; the formal statement proves that the max exists rather than assuming it
--   - generalization: there exists a vector of prices p → there exist prices p with p i ≥ 0 for all i; reason: a stronger conclusion: the prices found are nonnegative
--   - encoding: an n-buyer setting, [n] = {1, …, n} → 1 ≤ n, buyers Fin n (index i is buyer i + 1); reason: n ≥ 1 is the setting's standing range; q_n and r_n are undefined at n = 0
--   - encoding: 0 ≤ s(τ) ≤ min(H, 1/τ) → 0 ≤ s τ ∧ s τ ≤ H ∧ τ * s τ ≤ 1; reason: the same constraint at every τ ≥ 0
--   - encoding: revenues and probabilities as real expectations → values in [0, ∞] (lower integrals and measures); the factor 1/FR as an inverse in [0, ∞]; reason: Lean convention; a revenue cannot collapse to a junk value and no instance changes
-- source:
--   Beyhaghi et al., Improved Revenue Bounds for Posted-Price and Second-Price Mechanisms, arXiv:1807.03435v4, pp. 18–19, Theorem 3, (FR-Multi(H)); proof §8.3, pp. 33–35

import Mathlib
import Definitions.Def_SPPRevenue_SingleUnit_Setting
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_Programs
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_MultiUnit
import Definitions.Def_SPPRevenue_SingleUnit_Supplement_MultiProgram

namespace SPPRevenue.SingleUnit.Supplement

open MeasureTheory
open scoped ENNReal

theorem theorem_3 (H : ℕ) (hH : 1 ≤ H) :
    IsFactorProgram (frMultiValues H) ∧
    ENNReal.ofReal (1 - (H : ℝ) ^ H / ((H.factorial : ℝ) * Real.exp H)) < (frMulti H)⁻¹ ∧
    ∀ n : ℕ, 1 ≤ n → ∀ (μ : Fin n → Measure ℝ), (∀ i, IsProbabilityMeasure (μ i)) →
      ∀ (t : Fin n → (Fin n → ℝ) → ℝ), IsMultiThresholdMech H μ t → optRev μ t ≠ ⊤ →
        ∃ p : Fin n → ℝ, (∀ i, 0 ≤ p i) ∧ (frMulti H)⁻¹ * optRev μ t ≤ sppHRev H μ p := by sorry

end SPPRevenue.SingleUnit.Supplement
