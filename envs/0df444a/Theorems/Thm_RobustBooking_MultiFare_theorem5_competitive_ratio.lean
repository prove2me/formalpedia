-- Prove2me | Theorems.Thm_RobustBooking_MultiFare_theorem5_competitive_ratio
-- name    : RobustBooking.MultiFare.theorem5_competitive_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-03T00:02:20.058972+00:00
-- url     : https://prove2.me/theorems/a08446e5-c592-4470-a1fb-5ca869a9e912
-- title:
--   Theorem 5 — the nested policies A_θ and A′_θ with protection levels (7) have competitive ratio exactly 1/Δ
-- statement:
--   Consider the continuous $m$-fare booking problem with $m \ge 2$, fares $f_1 > f_2 > \dots > f_m > 0$ and capacity $n > 0$. Let $\Delta = m - \sum_{i=2}^m f_i/f_{i-1}$ (Eq. (6)), let $\theta$ be the protection levels of Eq. (7) and $Q$, $P$ the associated controls (Eqs. (8), (9)). Then the protection-level control policy $A_\theta$ and the order quantity control policy $A'_\theta$ both have competitive ratio exactly
--   $$c(A_\theta) = c(A'_\theta) = \frac{1}{\Delta}.$$
--   Together with Theorem 4 this says that nested booking with these protection levels is the best possible online policy for $m$ fare classes, deterministic or randomized. For $m = 2$, $f_2/f_1 = r$ it recovers the two-fare ratio $1/(2 - r)$.
--
--   **Formalization Note.** "Has competitive ratio $1/\Delta$" is stated as an equality of the competitive ratio (an infimum over all instances with positive offline optimum, with requests of any classes in any order and of any positive real size) with $1/\Delta$; both directions are part of the claim. The paper's §2.1 assumes $m \ge 3$; the statement is made for $m \ge 2$.
-- source:
--   Ball, Queyranne, Toward Robust Revenue Management: Competitive Analysis of Online Booking, Oper. Res. 57(4), 2009, p. 958, Theorem 5

import Mathlib
import Definitions.Def_RobustBooking_MultiFare_NestedPolicies

namespace RobustBooking.MultiFare

/-- Theorem 5 (p. 958): for the continuous `m`-fare problem (fares `f 1 > ⋯ > f m > 0`,
`m ≥ 2`, capacity `n > 0`), the booking policies `A_θ` and `A′_θ` with protection levels
defined by Eq. (7) have competitive ratio exactly `1/Δ`. -/
theorem theorem5_competitive_ratio (m : ℕ) (f : ℕ → ℝ) (n : ℝ) (hm : 2 ≤ m)
    (hf : StrictAntiOn f (Set.Icc 1 m)) (hfm : 0 < f m) (hn : 0 < n) :
    competitiveRatio m f n (protectionPolicy m f n) = 1 / Delta m f ∧
    competitiveRatio m f n (orderQuantityPolicy m f n) = 1 / Delta m f := by sorry

end RobustBooking.MultiFare
