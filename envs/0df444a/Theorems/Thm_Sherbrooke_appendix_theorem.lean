-- Prove2me | Theorems.Thm_Sherbrooke_appendix_theorem
-- name    : Sherbrooke.appendix_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:28:21.416517+00:00
-- url     : https://prove2.me/theorems/930fe6f0-9bfa-46fe-ba12-ec57b1be91b0
-- title:
--   METRIC Appendix Theorem: the marginal conditions (12) determine the optimal stock levels (corrected: $c_i>0$ or $\Xi_i$ attains its infimum)
-- statement:
--   Let $\iota$ be a finite set of items. For each item $i$ let $\Xi_i:\mathbb N\to\mathbb R$ be nonincreasing with a finite lower bound, let $\Xi_i'$ be its convexified function (the lower boundary of the convex hull of $\Xi_i$, so $\Xi_i'\le\Xi_i$), and let $c_i\ge0$ be a cost such that $c_i>0$ or $\Xi_i$ attains its infimum. Consider
--
--   $$
--   \min_{m}\ \sum_{i\in\iota}\bigl[c_im_i+\Xi_i(m_i)\bigr],\qquad m_i\in\{0,1,2,\dots\},\tag{11}
--   $$
--
--   and, for each item, the conditions (with $\Xi_i'(-1)=\infty$)
--
--   $$
--   c_i+\Xi_i'(\bar m_i+1)-\Xi_i'(\bar m_i)\ge0,\qquad c_i+\Xi_i'(\bar m_i)-\Xi_i'(\bar m_i-1)<0.\tag{12}
--   $$
--
--   Then
--
--   1. for each item $i$ there is exactly one $\bar m_i\in\mathbb N$ satisfying (12), and
--   2. every vector $\bar m$ whose coordinates satisfy (12) minimizes the original objective (11) over all stock vectors.
--
--   This is the optimality theorem behind the METRIC marginal-allocation procedure: stocking each item up to the level where one more unit no longer pays for itself, measured on the convexified backorder function, gives an optimal allocation for the original, possibly non-convex, backorder functions.
--
--   Differences from the source:
--
--   - correction: the {c_i} are nonnegative and not all zero → for each i, 0 ≤ c i and (0 < c i or Ξ_i attains its infimum); 'not all zero' dropped; reason: as printed the Theorem is false: ι = {1, 2}, c = (1, 0), Ξ_1 = Ξ_2 = 1/(m + 1) satisfy every hypothesis, yet (12) has no solution for item 2 and (11) has no minimizer; 'not all zero' plays no role in any step
--   - correction: unique optimizing {m̄_i} are determined by (12) → (a) (12) has exactly one solution per item, and (b) every solution vector of (12) minimizes (11); reason: the reading '(11) has a unique minimizer' is false: c = 1, Ξ = (2, 1, 0, 0, …) gives minimizers 0, 1, 2 of m + Ξ(m) while (12) holds only at 0; the proof shows (a) and (b)
--   - reading: monotonic decreasing → Antitone (nonincreasing); reason: the more general of the two readings; p. 136 justifies monotonicity only as 'cannot exceed'
--   - encoding: finite lower bound → BddBelow (Set.range Ξ); reason: same instances
--   - encoding: Ξ_i′ defined on the boundary of the convex hull of Ξ_i with Ξ_i′ ≤ Ξ_i → lowerHull Ξ m, the supremum of a m + b over all affine minorants k ↦ a k + b of Ξ on ℕ; reason: on ℕ this is the same function: the lower boundary of the convex hull of the points (k, Ξ(k)), equal to the greatest discretely convex minorant
--   - reading: Ξ′(m̄_i − 1) in the second line of (12) → Ξ_i′(m̄_i − 1), the convexified function of the same item; reason: the printed Ξ′ lacks the item index; Ξ_i′ is the only convexified function the line can refer to
--   - encoding: Define Ξ_i′(−1) = ∞ → the disjunct m = 0 in the second line of (12); reason: at m = 0 the line reads c + Ξ′(0) − ∞ < 0, which always holds; under m ≠ 0 the subtraction m − 1 is honest
--   - encoding: items i with costs c_i and stock levels m_i = 0, 1, 2, … → a Fintype ι, c : ι → ℝ, m : ι → ℕ; reason: same instances
-- source:
--   Sherbrooke, METRIC: A Multi-Echelon Technique for Recoverable Item Control, Operations Research 16 (1968), doi:10.1287/opre.16.1.122, Appendix, Theorem, eqs. (11)–(12), p. 140; proof pp. 140–141

import Mathlib
import Definitions.Def_Sherbrooke_lowerHull
import Definitions.Def_Sherbrooke_Cond12
import Definitions.Def_Sherbrooke_objective

namespace Sherbrooke

/-- **Appendix Theorem (corrected: `c_i > 0` or `Ξ_i` attains its infimum).** Sherbrooke,
*METRIC: A Multi-Echelon Technique for Recoverable Item Control*, Operations Research 16 (1968),
doi:10.1287/opre.16.1.122, Appendix, Theorem, p. 140: "Let Ξ_i(m_i) be a monotonic decreasing
function with a finite lower bound defined for m_i = 0, 1, 2, ···. Define Ξ_i′(m_i) on the boundary
of the convex hull of Ξ_i(m_i) such that Ξ_i′(m_i) ≤ Ξ_i(m_i). Suppose the objective is to find
the {m̄_i} which min_{m_i} Σ_i [c_i m_i + Ξ_i(m_i)], (m_i = 0, 1, 2, ···) (11) where the {c_i}
are nonnegative and not all zero. Then unique optimizing {m̄_i} are determined by
c_i + Ξ_i′(m̄_i + 1) − Ξ_i′(m̄_i) ≥ 0, c_i + Ξ_i′(m̄_i) − Ξ′(m̄_i − 1) < 0. (12)"

Let `ι` be a finite set of items, `Ξ_i : ℕ → ℝ` nonincreasing and bounded below, and
`c_i ≥ 0` with, for each item, `c_i > 0` or `Ξ_i` attaining its infimum. Then
(a) for each item `i`, condition (12) has exactly one solution `m̄_i ∈ ℕ`; and
(b) every vector `m̄` whose coordinates satisfy (12) minimizes the original objective (11),
`Σ_i [c_i m_i + Ξ_i(m_i)]`, over all stock vectors `m : ι → ℕ`.

**Formalization Note.** `Ξ_i′ = lowerHull (Ξ i)`, the supremum of the affine minorants of `Ξ_i`
on `ℕ`; `Ξ_i′(−1) = ∞` is encoded inside `Cond12`. Corrections: (1) as printed, with `c_i = 0`
allowed, the Theorem is false (`c = (1, 0)`, `Ξ_1 = Ξ_2 = 1/(m+1)`: (12) has no solution for
item 2 and (11) has no minimizer); the per-item hypothesis "`c_i > 0` or `Ξ_i` attains its
infimum" is the minimal repair, and "not all zero" is dropped as it plays no role. (2) "unique
optimizing {m̄_i} are determined by (12)" is read as (a) + (b): the reading "(11) has a unique
minimizer" is false (`c = 1`, `Ξ = (2, 1, 0, 0, …)` has minimizers 0, 1, 2 while (12) holds only
at 0). The typo `Ξ′(m̄_i − 1)` in (12) is read as `Ξ_i′(m̄_i − 1)`. -/
theorem appendix_theorem {ι : Type*} [Fintype ι] (c : ι → ℝ) (Ξ : ι → ℕ → ℝ)
    (hanti : ∀ i, Antitone (Ξ i)) (hbdd : ∀ i, BddBelow (Set.range (Ξ i)))
    (hc : ∀ i, 0 ≤ c i)
    (hcorr : ∀ i, 0 < c i ∨ ∃ m₀ : ℕ, ∀ k : ℕ, Ξ i m₀ ≤ Ξ i k) :
    (∀ i, ∃! m : ℕ, Cond12 (c i) (Ξ i) m) ∧
      ∀ mbar : ι → ℕ, (∀ i, Cond12 (c i) (Ξ i) (mbar i)) →
        ∀ m : ι → ℕ, objective c Ξ mbar ≤ objective c Ξ m := by sorry

end Sherbrooke
