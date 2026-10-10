-- Prove2me | Theorems.Thm_StrictCQ_Scaled_scaled_akkt_linear
-- name    : StrictCQ.Scaled.scaled_akkt_linear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:57:55.35698+00:00
-- url     : https://prove2.me/theorems/414b4f6f-1617-4c9f-995d-b362c7da6a46
-- title:
--   §2, p. 4 — the multipliers kλ, kμ make Scaled-AKKT hold for every linear objective
-- statement:
--   Let $h_1,\dots,h_m$, $g_1,\dots,g_p$ be a constraint system on $\mathbb R^n$ and $x^*$ a feasible point. Suppose $\lambda \in \mathbb R^m$ and $\mu \in \mathbb R^p$ satisfy $\mu_j \ge 0$ for all $j$, $\mu_j = 0$ whenever $g_j(x^*) \ne 0$, $\max\{\|\lambda\|_\infty, \|\mu\|_\infty\} = 1$, and (2.4):
--
--   $$
--   \sum_{i=1}^m \lambda_i \nabla h_i(x^*) + \sum_{j:\, g_j(x^*) = 0} \mu_j \nabla g_j(x^*) = 0 .
--   $$
--
--   Then for every $c \in \mathbb R^n$ the Scaled-AKKT condition holds at $x^*$ for the linear objective $f(x) = \langle x, c\rangle$.
--
--   In the paper this is witnessed by the constant sequence $x^k = x^*$ with multipliers $k\lambda$ and $k\mu$; it is the construction that shows (2.3) is the weakest strict constraint qualification for Scaled-AKKT.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 4, §2 (last paragraph of §2)

import Mathlib
import Definitions.Def_StrictCQ_Scaled_Setting
import Definitions.Def_StrictCQ_Scaled_Conditions

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.Scaled

theorem scaled_akkt_linear {n m p : ℕ} (C : Constraints n m p)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible)
    (l : Fin m → ℝ) (u : Fin p → ℝ) (hu : ∀ j, 0 ≤ u j) (hcomp : ∀ j, C.g j xs ≠ 0 → u j = 0)
    (hnorm : max ‖l‖ ‖u‖ = 1)
    (h24 : ∑ i, l i • gradient (C.h i) xs + ∑ j, u j • gradient (C.g j) xs = 0)
    (c : EuclideanSpace ℝ (Fin n)) :
    C.ScaledAKKT (fun x => ⟪x, c⟫_ℝ) xs := by sorry

end StrictCQ.Scaled
