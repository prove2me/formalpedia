-- Prove2me | Theorems.Thm_SilverRateSC_lemma_5_4
-- name    : SilverRateSC.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:46:36.357438+00:00
-- url     : https://prove2.me/theorems/33c1e3cf-7113-4399-ad84-6229740982bd
-- title:
--   Lemma 5.4 — $\min\{D_{n,\kappa}(H),E_{n,\kappa}(H)\}\ge\exp[-(Cn/m)\log(m+1)]$
-- statement:
--   Under the hypotheses of Proposition 5.3, with its $m$ and $C$: for every integer $n\ge1$ and every schedule $H\in[0,\infty)^n$,
--   $$\min\{D_{n,\kappa}(H),E_{n,\kappa}(H)\}\ge\exp\Bigl[-\frac{Cn}m\log(m+1)\Bigr].$$
--
--   Repeating the schedule removes the horizon-independent factor $\exp[-C\log(m+1)]$ of Proposition 5.3 and extends the bound to function suboptimality.
--
--   Differences from the source:
--   - encoding: let m and C be as in Proposition 5.3 → one statement ∃ c_* C ξ > 0 asserting, for all β, κ, H under (24), S_0 ≥ 1, m ≥ 1, both (25) and (28) with the same C and m; reason: standalone form of the reference to Proposition 5.3's constants
--   - encoding: H = (h_1, …, h_n) ∈ [0,∞)^n with n ≥ 1 → H : List ℝ with nonnegative entries and n = H.length ≥ 1; reason: same schedules
--   - encoding: D_{n,κ}(H), E_{n,κ}(H) as suprema of real ratios → worstDist, worstGap valued in ℝ≥0∞; the bound is ENNReal.ofReal of the real right-hand side; reason: the suprema are finite (proved in the verification file), so the comparison is the paper's
--   - encoding: F_{1/κ,1}(ℝ^d) → HighResODE.NAGSC.IsS1 F κ⁻¹ 1, which also asks 0 < κ⁻¹ ≤ 1; reason: identical for κ ≥ 1; for κ < 1 the paper's class is empty in every dimension d ≥ 1 as well
--   - reading: log (base not stated) → natural logarithm Real.log; reason: the paper pairs log with exp; another base changes only the constants
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), Lemma 5.4, p.23; hypotheses of Proposition 5.3, p.21

import Mathlib
import Definitions.Def_SilverRateSC_pOf
import Definitions.Def_SilverRateSC_aBeta
import Definitions.Def_SilverRateSC_worstDist
import Definitions.Def_SilverRateSC_worstGap

open scoped ENNReal

namespace SilverRateSC

/-- **Lemma 5.4.** Under the hypotheses of Proposition 5.3, let `m` and `C` be as there. For every
integer `n ≥ 1` and every schedule `H ∈ [0, ∞)^n`,
`min{D_{n,κ}(H), E_{n,κ}(H)} ≥ exp[−(Cn/m) log(m + 1)]` (28).

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, Lemma 5.4, p. 23 (hypotheses of Proposition 5.3, p. 21).

**Formalization Note** "Let `m` and `C` be as there" is made standalone: the constants
`c_*, C, ξ > 0` are quantified once and both (25) (Proposition 5.3) and (28) are asserted with
the same `C` and `m = ⌊c_*(κ/a_β)^{1/p(c_β)}⌋`, `S_0 = ξκ`. `D_{n,κ}`, `E_{n,κ}` are `worstDist`,
`worstGap` in `ℝ≥0∞`. -/
theorem lemma_5_4 :
    ∃ cs C ξ : ℝ, 0 < cs ∧ 0 < C ∧ 0 < ξ ∧
      ∀ β κ : ℝ, 0 < β → β ≤ 1 / 4 → 4 ≤ κ →
        1 ≤ ξ * κ → 1 ≤ ⌊cs * (κ / aBeta β) ^ (1 / pOf (cBeta β))⌋₊ →
        ∀ H : List ℝ, 1 ≤ H.length → (∀ x ∈ H, 0 ≤ x) →
          ENNReal.ofReal (Real.exp (-C * (1 + (H.length : ℝ) /
              ⌊cs * (κ / aBeta β) ^ (1 / pOf (cBeta β))⌋₊) *
              Real.log (⌊cs * (κ / aBeta β) ^ (1 / pOf (cBeta β))⌋₊ + 1))) ≤
            worstDist κ H ∧
          ENNReal.ofReal (Real.exp (-(C * H.length /
              ⌊cs * (κ / aBeta β) ^ (1 / pOf (cBeta β))⌋₊) *
              Real.log (⌊cs * (κ / aBeta β) ^ (1 / pOf (cBeta β))⌋₊ + 1))) ≤
            min (worstDist κ H) (worstGap κ H) := by sorry

end SilverRateSC
