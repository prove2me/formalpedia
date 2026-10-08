-- Prove2me | Theorems.Thm_VeinottNoDiscount_Overtake_display_y_telescoping
-- name    : VeinottNoDiscount.Overtake.display_y_telescoping
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:51:45.544224+00:00
-- url     : https://prove2.me/theorems/6ce6b0c3-e743-4501-bfe5-f5cbbe6cbb9b
-- title:
--   §5, p. 1293 — y(f) = Σ_{i<n} Q(f)^i[r(f) − x(f)] + Q(f)ⁿy(f) = Vⁿ(f^∞) − nx(f) + Q(f)ⁿy(f)
-- statement:
--   Let $f\in F$ be a decision rule with income vector $r(f)$, transition matrix $Q(f)$, gain $x(f)$ and bias $y(f)$, and let $V^n(f^\infty)$ be the vector of total expected returns in the first $n$ periods under the stationary policy $f^\infty$. Then
--   $$y(f)=r(f)-x(f)+Q(f)\,y(f),$$
--   and, iterating, for every $n\ge0$,
--   $$y(f)=\sum_{i=0}^{n-1}Q(f)^i\,[r(f)-x(f)]+Q(f)^n\,y(f)=V^n(f^\infty)-n\,x(f)+Q(f)^n\,y(f).$$
--
--   The identity expresses the bias as the $n$-period return in excess of $n$ times the gain, corrected by the bias at the end of period $n$; averaging it over $n$ gives the representations (27) and (28).
--
--   **Formalization Note** $x(f)$ and $y(f)$ are the published closed forms $Q^*(f)r(f)$ and $H(f)r(f)$. At $n=0$ both iterated identities read $y(f)=y(f)$.
-- source:
--   Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting, Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1293, §5, unnumbered display before (27)

import Mathlib
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_BlackwellDiscreteDP_NearOne_Model
import Definitions.Def_BlackwellDiscreteDP_NearOne_GainBias
import Definitions.Def_VeinottNoDiscount_Overtake_Criteria
open Filter Topology Matrix BlackwellDiscreteDP.NearOne

namespace VeinottNoDiscount.Overtake

/-- **§5, display before (27).** "Observe from the definitions of x(f) and y(f) that
`y(f) = r(f) − x(f) + Q(f)y(f) = ⋯ = Σ_{i=0}^{n−1} Q(f)^i[r(f) − x(f)] + Q(f)^n y(f)
= V^n(f^∞) − nx(f) + Q(f)^n y(f)`."

Veinott, On Finding Optimal Policies in Discrete Dynamic Programming with No Discounting,
Ann. Math. Statist. 37(5):1284–1294 (1966), DOI 10.1214/aoms/1177699272, p. 1293, §5 (unnumbered display).

**Formalization Note.** `x(f)`, `y(f)` are the published closed forms `Q*(f)r(f)` and
`H(f)r(f)` (Blackwell's Theorem 3 / published `theorem_4a` says they are the unique solutions
of (2), (3)). The three equalities of the display are the three conjuncts, the last two for every
`n : ℕ` (at `n = 0` they read `y(f) = y(f)`). `nx(f)` is `(n : ℝ) • x(f)`. -/
theorem display_y_telescoping {St Act : Type*} [Fintype St] [DecidableEq St] [Nonempty St]
    [Fintype Act] [Nonempty Act] (M : Model St Act)
    (f : St → Act) :
    M.y f = M.r f - M.x f + M.Q f *ᵥ M.y f ∧
      (∀ n : ℕ, M.y f = (∑ i ∈ Finset.range n, (M.Q f ^ i) *ᵥ (M.r f - M.x f))
        + (M.Q f ^ n) *ᵥ M.y f) ∧
      (∀ n : ℕ, M.y f = Vn M (Policy.stationary f) n - (n : ℝ) • M.x f
        + (M.Q f ^ n) *ᵥ M.y f) := by sorry

end VeinottNoDiscount.Overtake
