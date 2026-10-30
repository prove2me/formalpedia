-- Prove2me | Theorems.Thm_Sherbrooke_cond12_exists
-- name    : Sherbrooke.cond12_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:25:33.11678+00:00
-- url     : https://prove2.me/theorems/d2eae8ec-d980-4e8d-863f-343e6437d015
-- title:
--   Equation (12) has a solution (corrected: $c>0$ or $\Xi$ attains its infimum)
-- statement:
--   Fix one item with cost $c\ge0$ and $\Xi:\mathbb N\to\mathbb R$ nonincreasing and bounded below, and let $\Xi'$ be the convexified function. Assume that $c>0$ or that $\Xi$ attains its infimum (some $m_0$ has $\Xi(m_0)\le\Xi(k)$ for all $k$). Then some $\bar m\in\mathbb N$ satisfies condition (12):
--
--   $$
--   c+\Xi'(\bar m+1)-\Xi'(\bar m)\ge0,\qquad c+\Xi'(\bar m)-\Xi'(\bar m-1)<0\quad(\Xi'(-1)=\infty).
--   $$
--
--   This is the existence half of the Appendix Theorem's claim that (12) determines the optimal stock level.
--
--   Differences from the source:
--
--   - correction: (12) has at least one solution for any nonnegative value of c_i → hypothesis 0 < c ∨ ∃ m₀, ∀ k, Ξ m₀ ≤ Ξ k added; reason: as printed it is false: c = 0 and Ξ(m) = 1/(m + 1), which is convex so Ξ′ = Ξ, give Ξ′(m + 1) − Ξ′(m) < 0 for every m, so the first line of (12) never holds
--   - encoding: one item i with cost c_i and function Ξ_i → c : ℝ, Ξ : ℕ → ℝ, stock level m : ℕ; reason: the proof treats a single item ('we can disregard the summation sign')
--   - reading: monotonic decreasing → Antitone (nonincreasing); reason: the more general of the two readings; p. 136 justifies monotonicity only as 'cannot exceed'
--   - encoding: Ξ_i′ defined on the boundary of the convex hull of Ξ_i with Ξ_i′ ≤ Ξ_i → lowerHull Ξ m, the supremum of a m + b over all affine minorants k ↦ a k + b of Ξ on ℕ; reason: on ℕ this is the same function: the lower boundary of the convex hull of the points (k, Ξ(k)), equal to the greatest discretely convex minorant
--   - encoding: finite lower bound → BddBelow (Set.range Ξ); reason: same instances
--   - reading: Ξ′(m̄_i − 1) in the second line of (12) → Ξ_i′(m̄_i − 1), the convexified function of the same item; reason: the printed Ξ′ lacks the item index; Ξ_i′ is the only convexified function the line can refer to
--   - encoding: Define Ξ_i′(−1) = ∞ → the disjunct m = 0 in the second line of (12); reason: at m = 0 the line reads c + Ξ′(0) − ∞ < 0, which always holds; under m ≠ 0 the subtraction m − 1 is honest
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Operations Research 16 (1968), doi:10.1287/opre.16.1.122, Appendix, proof of the Theorem, p. 140 ("Define Ξ_i′(−1) = ∞. ... This shows that equation (12) has at least one solution for any nonnegative value of c_i.")

import Mathlib
import Definitions.Def_Sherbrooke_lowerHull
import Definitions.Def_Sherbrooke_Cond12

namespace Sherbrooke

/-- **M5: equation (12) has a solution (corrected).** Sherbrooke, *METRIC*, Operations Research
16 (1968), Appendix, proof of the Theorem, p. 140: "Define Ξ_i′(−1) = ∞. We use the fact that a
monotonically decreasing sequence bounded below has a limit. This shows that equation (12) has at
least one solution for any nonnegative value of c_i."

If `Ξ : ℕ → ℝ` is nonincreasing and bounded below, `c ≥ 0`, and either `c > 0` or `Ξ` attains
its infimum, then some `m ∈ ℕ` satisfies condition (12).

**Formalization Note (correction).** As printed ("for any nonnegative value of c_i") the claim is
false: for `c = 0` and `Ξ(m) = 1/(m+1)`, which is convex so `Ξ′ = Ξ`, the first line of (12)
needs `Ξ′(m+1) − Ξ′(m) ≥ 0`, which never holds. The added hypothesis
`0 < c ∨ ∃ m₀, ∀ k, Ξ m₀ ≤ Ξ k` is exactly what excludes this case. -/
theorem cond12_exists (c : ℝ) (Ξ : ℕ → ℝ) (hanti : Antitone Ξ)
    (hbdd : BddBelow (Set.range Ξ)) (hc : 0 ≤ c)
    (hcorr : 0 < c ∨ ∃ m₀ : ℕ, ∀ k : ℕ, Ξ m₀ ≤ Ξ k) :
    ∃ m : ℕ, Cond12 c Ξ m := by sorry

end Sherbrooke
