-- Prove2me | Theorems.Thm_Sherbrooke_cond12_unique
-- name    : Sherbrooke.cond12_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:26:07.574879+00:00
-- url     : https://prove2.me/theorems/3ba46808-5827-42ec-be1a-2828ff4b0f14
-- title:
--   Equation (12) has at most one solution
-- statement:
--   Fix one item with cost $c\in\mathbb R$ and $\Xi:\mathbb N\to\mathbb R$ bounded below, and let $\Xi'$ be the convexified function. If both $m$ and $n$ satisfy condition (12) with the same cost $c$, then $m=n$.
--
--   In the proof of the Appendix Theorem: (12) makes the three points $\Xi_i'(\bar m_i-1)$, $\Xi_i'(\bar m_i)$, $\Xi_i'(\bar m_i+1)$ strictly convex, and since $\Xi_i'$ is convex the solution is unique.
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
--   - reading: Ξ_i′(m̄_{i−1}) → Ξ_i′(m̄_i − 1); reason: the three consecutive points of the strict-convexity claim; the stock level of another item i − 1 has no role in a single-item argument
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Operations Research 16 (1968), doi:10.1287/opre.16.1.122, Appendix, proof of the Theorem, p. 140 ("But equation (12) implies that the set of points Ξ_i′(m̄_{i−1}), Ξ_i′(m̄_i), and Ξ_i′(m̄_i + 1) is strictly convex. Since the function Ξ_i′ is convex, m̄_i is unique.")

import Mathlib
import Definitions.Def_Sherbrooke_lowerHull
import Definitions.Def_Sherbrooke_Cond12

namespace Sherbrooke

/-- **M6: equation (12) has at most one solution.** Sherbrooke, *METRIC*, Operations Research 16
(1968), Appendix, proof of the Theorem, p. 140: "But equation (12) implies that the set of points
Ξ_i′(m̄_i − 1), Ξ_i′(m̄_i), and Ξ_i′(m̄_i + 1) is strictly convex. Since the function Ξ_i′ is
convex, m̄_i is unique."

If `Ξ : ℕ → ℝ` is bounded below and both `m` and `n` satisfy condition (12) with the same cost
`c`, then `m = n`.

**Formalization Note.** The page prints "Ξ_i′(m̄_{i−1})"; it is read as `Ξ_i′(m̄_i − 1)`, the
point the strict-convexity claim needs. The standing hypotheses "Ξ monotonic decreasing" and
"c nonnegative" are not needed for this step and are dropped (a generalization). -/
theorem cond12_unique (c : ℝ) (Ξ : ℕ → ℝ) (hbdd : BddBelow (Set.range Ξ)) (m n : ℕ)
    (hm : Cond12 c Ξ m) (hn : Cond12 c Ξ n) : m = n := by sorry

end Sherbrooke
