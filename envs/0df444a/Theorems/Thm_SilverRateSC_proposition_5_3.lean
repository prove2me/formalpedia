-- Prove2me | Theorems.Thm_SilverRateSC_proposition_5_3
-- name    : SilverRateSC.proposition_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:46:17.594649+00:00
-- url     : https://prove2.me/theorems/a674750f-063a-4bf2-8dee-db5b6aef6826
-- title:
--   Proposition 5.3 — $D_{n,\kappa}(H)\ge\exp[-C(1+n/m)\log(m+1)]$ for fixed $\beta$
-- statement:
--   There exist absolute constants $c_*,C,\xi>0$ with the following property. For every $0<\beta\le1/4$ and $\kappa\ge4$, set
--   $$S_0:=\xi\kappa,\qquad m:=\bigl\lfloor c_*(\kappa/a_\beta)^{1/p(c_\beta)}\bigr\rfloor.$$
--   If $S_0\ge1$ and $m\ge1$, then every horizon $n\ge1$ and every nonnegative schedule $H\in[0,\infty)^n$ satisfy
--   $$D_{n,\kappa}(H)\ge\exp\Bigl[-C\Bigl(1+\frac nm\Bigr)\log(m+1)\Bigr].$$
--
--   This is the global lower bound obtained by assembling bending, bridging and repair components into one hard function for the given schedule.
--
--   Differences from the source:
--   - encoding: absolute constants c_*, C, ξ; m = ⌊·⌋ → ∃ c_* C ξ quantified before β, κ, H; m = Nat.floor; reason: same
--   - encoding: H = (h_1, …, h_n) ∈ [0,∞)^n with n ≥ 1 → H : List ℝ with nonnegative entries and n = H.length ≥ 1; reason: same schedules
--   - encoding: D_{n,κ}(H), E_{n,κ}(H) as suprema of real ratios → worstDist, worstGap valued in ℝ≥0∞; the bound is ENNReal.ofReal of the real right-hand side; reason: the suprema are finite (proved in the verification file), so the comparison is the paper's
--   - encoding: F_{1/κ,1}(ℝ^d) → HighResODE.NAGSC.IsS1 F κ⁻¹ 1, which also asks 0 < κ⁻¹ ≤ 1; reason: identical for κ ≥ 1; for κ < 1 the paper's class is empty in every dimension d ≥ 1 as well
--   - reading: log (base not stated) → natural logarithm Real.log; reason: the paper pairs log with exp; another base changes only the constants
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), Proposition 5.3, p.21

import Mathlib
import Definitions.Def_SilverRateSC_pOf
import Definitions.Def_SilverRateSC_aBeta
import Definitions.Def_SilverRateSC_worstDist

open scoped ENNReal

namespace SilverRateSC

/-- **Proposition 5.3 (Global lower bound for fixed `β`).** There exist absolute constants
`c_*, C, ξ > 0` with the following property. For every `0 < β ≤ 1/4` and `κ ≥ 4`, set
`S_0 := ξκ`, `m := ⌊c_*(κ/a_β)^{1/p(c_β)}⌋` (24). If `S_0 ≥ 1` and `m ≥ 1`, then every horizon
`n ≥ 1` and every nonnegative schedule `H` satisfy `D_{n,κ}(H) ≥ exp[−C(1 + n/m) log(m + 1)]` (25).

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, Proposition 5.3, p. 21.

**Formalization Note** `c_*, C, ξ` precede `β, κ`. `m` is `Nat.floor`, `log` is natural, the
schedule is a `List ℝ` with nonnegative entries and `n` its length, and `D_{n,κ}` is `worstDist`
(in `ℝ≥0∞`, so the bound is `ENNReal.ofReal` of the real right-hand side). -/
theorem proposition_5_3 :
    ∃ cs C ξ : ℝ, 0 < cs ∧ 0 < C ∧ 0 < ξ ∧
      ∀ β κ : ℝ, 0 < β → β ≤ 1 / 4 → 4 ≤ κ →
        1 ≤ ξ * κ → 1 ≤ ⌊cs * (κ / aBeta β) ^ (1 / pOf (cBeta β))⌋₊ →
        ∀ H : List ℝ, 1 ≤ H.length → (∀ x ∈ H, 0 ≤ x) →
          ENNReal.ofReal (Real.exp (-C * (1 + (H.length : ℝ) /
              ⌊cs * (κ / aBeta β) ^ (1 / pOf (cBeta β))⌋₊) *
              Real.log (⌊cs * (κ / aBeta β) ^ (1 / pOf (cBeta β))⌋₊ + 1))) ≤
            worstDist κ H := by sorry

end SilverRateSC
