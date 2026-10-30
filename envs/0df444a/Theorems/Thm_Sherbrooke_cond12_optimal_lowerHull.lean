-- Prove2me | Theorems.Thm_Sherbrooke_cond12_optimal_lowerHull
-- name    : Sherbrooke.cond12_optimal_lowerHull
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:24:18.082879+00:00
-- url     : https://prove2.me/theorems/f093a51a-52a3-4775-8305-331eec57d51d
-- title:
--   A solution of (12) minimizes $c\,m+\Xi'(m)$
-- statement:
--   Fix one item with cost $c\in\mathbb R$ and $\Xi:\mathbb N\to\mathbb R$ bounded below, and let $\Xi'$ be the convexified function. If $\bar m$ satisfies condition (12), then $\bar m$ solves (11) for $\Xi'$:
--
--   $$
--   c\,\bar m+\Xi'(\bar m)\ \le\ c\,k+\Xi'(k)\qquad\text{for every }k\in\mathbb N .
--   $$
--
--   In the proof of the Appendix Theorem this is the observation that (12) is a local optimality condition for the convex function $c\,m+\Xi'(m)$.
--
--   Differences from the source:
--
--   - generalization: Ξ_i monotonic decreasing (standing hypothesis) → hypothesis dropped; reason: this step does not use it; the statement specializes to the source's setting by adding it
--   - generalization: c_i nonnegative (standing hypothesis) → hypothesis dropped; reason: this step does not use it; the statement specializes to the source's setting by adding it
--   - encoding: one item i with cost c_i and function Ξ_i → c : ℝ, Ξ : ℕ → ℝ, stock level m : ℕ; reason: the proof treats a single item ('we can disregard the summation sign')
--   - encoding: Ξ_i′ defined on the boundary of the convex hull of Ξ_i with Ξ_i′ ≤ Ξ_i → lowerHull Ξ m, the supremum of a m + b over all affine minorants k ↦ a k + b of Ξ on ℕ; reason: on ℕ this is the same function: the lower boundary of the convex hull of the points (k, Ξ(k)), equal to the greatest discretely convex minorant
--   - encoding: finite lower bound → BddBelow (Set.range Ξ); reason: same instances
--   - reading: Ξ′(m̄_i − 1) in the second line of (12) → Ξ_i′(m̄_i − 1), the convexified function of the same item; reason: the printed Ξ′ lacks the item index; Ξ_i′ is the only convexified function the line can refer to
--   - encoding: Define Ξ_i′(−1) = ∞ → the disjunct m = 0 in the second line of (12); reason: at m = 0 the line reads c + Ξ′(0) − ∞ < 0, which always holds; under m ≠ 0 the subtraction m − 1 is honest
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Operations Research 16 (1968), doi:10.1287/opre.16.1.122, Appendix, proof of the Theorem, p. 140 ("It is clear that if {m̄_i} exist that satisfy equation (12), then equation (11) is solved for Ξ_i′.")

import Mathlib
import Definitions.Def_Sherbrooke_lowerHull
import Definitions.Def_Sherbrooke_Cond12

namespace Sherbrooke

/-- **M3: a solution of (12) solves (11) for `Ξ′`.** Sherbrooke, *METRIC*, Operations Research
16 (1968), Appendix, proof of the Theorem, p. 140: "It is clear that if {m̄_i} exist that satisfy
equation (12), then equation (11) is solved for Ξ_i′."

For one item: if `Ξ : ℕ → ℝ` is bounded below and `m̄` satisfies condition (12) with cost
`c`, then `m̄` minimizes `k ↦ c k + Ξ′(k)` over all `k ∈ ℕ`, where `Ξ′ = lowerHull Ξ`.

**Formalization Note.** Stated for one item (the objective separates, M2). The standing
hypotheses "Ξ monotonic decreasing" and "c nonnegative" are not needed for this step and are
dropped (a generalization). -/
theorem cond12_optimal_lowerHull (c : ℝ) (Ξ : ℕ → ℝ) (hbdd : BddBelow (Set.range Ξ))
    (mbar : ℕ) (h12 : Cond12 c Ξ mbar) :
    ∀ k : ℕ, c * (mbar : ℝ) + lowerHull Ξ mbar ≤ c * (k : ℝ) + lowerHull Ξ k := by sorry

end Sherbrooke
