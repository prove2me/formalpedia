-- Prove2me | Theorems.Thm_Sherbrooke_cond12_optimal
-- name    : Sherbrooke.cond12_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:27:48.039988+00:00
-- url     : https://prove2.me/theorems/9ec41d77-f76d-49ea-93ce-bd1c0f2a7dff
-- title:
--   A solution of (12) minimizes $c\,m+\Xi(m)$ for the original $\Xi$
-- statement:
--   Fix one item with cost $c\in\mathbb R$ and $\Xi:\mathbb N\to\mathbb R$ nonincreasing and bounded below, and let $\Xi'$ be the convexified function. If $\bar m$ satisfies condition (12), then $\bar m$ minimizes the original single-item objective:
--
--   $$
--   c\,\bar m+\Xi(\bar m)\ \le\ c\,k+\Xi(k)\qquad\text{for every }k\in\mathbb N .
--   $$
--
--   This is the last step of the proof of the Appendix Theorem: replacing $\Xi$ by $\Xi'\le\Xi$ can only lower the minimum, and at a solution of (12) the two functions agree.
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
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Operations Research 16 (1968), doi:10.1287/opre.16.1.122, Appendix, proof of the Theorem, pp. 140–141 ("Replacing Ξ_i(m_i) by Ξ_i′(m_i) can only decrease the minimum in equation (11), but as we have just seen any m̄_i satisfying equation (12) implies that at point Ξ_i(m̄_i) = Ξ_i′(m̄_i), solving the original problem.")

import Mathlib
import Definitions.Def_Sherbrooke_lowerHull
import Definitions.Def_Sherbrooke_Cond12

namespace Sherbrooke

/-- **M9: a solution of (12) is optimal for the original `Ξ`.** Sherbrooke, *METRIC*, Operations
Research 16 (1968), Appendix, proof of the Theorem, pp. 140–141: "Replacing Ξ_i(m_i) by Ξ_i′(m_i)
can only decrease the minimum in equation (11), but as we have just seen any m̄_i satisfying
equation (12) implies that at point Ξ_i(m̄_i) = Ξ_i′(m̄_i), solving the original problem."

For one item: if `Ξ : ℕ → ℝ` is nonincreasing and bounded below and `m̄` satisfies condition
(12) with cost `c`, then `m̄` minimizes `k ↦ c k + Ξ(k)` over all `k ∈ ℕ`.

**Formalization Note.** The conclusion is about the original `Ξ`, not `Ξ′`. The standing
hypothesis "c nonnegative" is not needed for this step and is dropped (a generalization). -/
theorem cond12_optimal (c : ℝ) (Ξ : ℕ → ℝ) (hanti : Antitone Ξ)
    (hbdd : BddBelow (Set.range Ξ)) (mbar : ℕ) (h12 : Cond12 c Ξ mbar) :
    ∀ k : ℕ, c * (mbar : ℝ) + Ξ mbar ≤ c * (k : ℝ) + Ξ k := by sorry

end Sherbrooke
