-- Prove2me | Theorems.Thm_Sherbrooke_lowerHull_eq_of_cond12
-- name    : Sherbrooke.lowerHull_eq_of_cond12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:27:18.370484+00:00
-- url     : https://prove2.me/theorems/359e896e-6494-467c-8c2c-3c6505db2945
-- title:
--   At a solution of (12), $\Xi'=\Xi$
-- statement:
--   Fix one item with cost $c\in\mathbb R$ and $\Xi:\mathbb N\to\mathbb R$ nonincreasing and bounded below, and let $\Xi'$ be the convexified function. If $\bar m$ satisfies condition (12), then
--
--   $$
--   \Xi'(\bar m)=\Xi(\bar m).
--   $$
--
--   In the words of the proof of the Appendix Theorem, "the artificial point $m_i$ cannot satisfy equation (12)"; p. 136 states the same: "In order for $m$ to be a solution, $\Xi_i'(m)$ must equal $\Xi_i(m)$".
--
--   Differences from the source:
--
--   - generalization: c_i nonnegative (standing hypothesis) → hypothesis dropped; reason: this step does not use it; the statement specializes to the source's setting by adding it
--   - encoding: one item i with cost c_i and function Ξ_i → c : ℝ, Ξ : ℕ → ℝ, stock level m : ℕ; reason: the proof treats a single item ('we can disregard the summation sign')
--   - reading: monotonic decreasing → Antitone (nonincreasing); reason: the more general of the two readings; p. 136 justifies monotonicity only as 'cannot exceed'
--   - encoding: Ξ_i′ defined on the boundary of the convex hull of Ξ_i with Ξ_i′ ≤ Ξ_i → lowerHull Ξ m, the supremum of a m + b over all affine minorants k ↦ a k + b of Ξ on ℕ; reason: on ℕ this is the same function: the lower boundary of the convex hull of the points (k, Ξ(k)), equal to the greatest discretely convex minorant
--   - encoding: finite lower bound → BddBelow (Set.range Ξ); reason: same instances
--   - reading: Ξ′(m̄_i − 1) in the second line of (12) → Ξ_i′(m̄_i − 1), the convexified function of the same item; reason: the printed Ξ′ lacks the item index; Ξ_i′ is the only convexified function the line can refer to
--   - encoding: Define Ξ_i′(−1) = ∞ → the disjunct m = 0 in the second line of (12); reason: at m = 0 the line reads c + Ξ′(0) − ∞ < 0, which always holds; under m ≠ 0 the subtraction m − 1 is honest
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Operations Research 16 (1968), doi:10.1287/opre.16.1.122, Appendix, proof of the Theorem, p. 140 ("And thus, the artificial point m_i cannot satisfy equation (12)."); also p. 136

import Mathlib
import Definitions.Def_Sherbrooke_lowerHull
import Definitions.Def_Sherbrooke_Cond12

namespace Sherbrooke

/-- **M8: a solution of (12) is not an artificial point.** Sherbrooke, *METRIC*, Operations
Research 16 (1968), Appendix, proof of the Theorem, p. 140: "And thus, the artificial point m_i
cannot satisfy equation (12)." Also p. 136: "In order for m to be a solution, Ξ_i′(m) must equal
Ξ_i(m)".

If `Ξ : ℕ → ℝ` is nonincreasing and bounded below and `m` satisfies condition (12) with cost
`c`, then `Ξ′(m) = Ξ(m)`, where `Ξ′ = lowerHull Ξ`.

**Formalization Note.** "Monotonic decreasing" is read as `Antitone`. The standing hypothesis
"c nonnegative" is not needed for this step and is dropped (a generalization). -/
theorem lowerHull_eq_of_cond12 (c : ℝ) (Ξ : ℕ → ℝ) (hanti : Antitone Ξ)
    (hbdd : BddBelow (Set.range Ξ)) (m : ℕ) (h12 : Cond12 c Ξ m) :
    lowerHull Ξ m = Ξ m := by sorry

end Sherbrooke
