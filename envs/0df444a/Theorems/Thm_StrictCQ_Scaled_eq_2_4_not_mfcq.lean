-- Prove2me | Theorems.Thm_StrictCQ_Scaled_eq_2_4_not_mfcq
-- name    : StrictCQ.Scaled.eq_2_4_not_mfcq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:57:44.21488+00:00
-- url     : https://prove2.me/theorems/879b1c17-4690-4bb6-9221-fc6571c6e2f6
-- title:
--   §2, p. 4 — a nonzero solution of (2.4) contradicts MFCQ
-- statement:
--   Let $h_1,\dots,h_m$, $g_1,\dots,g_p$ be a constraint system on $\mathbb R^n$ and $x^*$ a feasible point. Suppose there are $\lambda \in \mathbb R^m$ and $\mu \in \mathbb R^p$ with $\mu_j \ge 0$ for all $j$, $\mu_j = 0$ whenever $g_j(x^*) \ne 0$, $\max\{\|\lambda\|_\infty, \|\mu\|_\infty\} = 1$, and
--
--   $$
--   \sum_{i=1}^m \lambda_i \nabla h_i(x^*) + \sum_{j:\, g_j(x^*) = 0} \mu_j \nabla g_j(x^*) = 0 .
--   $$
--
--   Then $x^*$ does not satisfy the Mangasarian–Fromovitz constraint qualification.
--
--   Combined with the previous milestone, this closes the proof that (2.3) is a strict constraint qualification associated with Scaled-AKKT.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 4, §2 (sentence after (2.4))

import Mathlib
import Definitions.Def_StrictCQ_Scaled_Setting
import Definitions.Def_StrictCQ_Scaled_Conditions

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.Scaled

theorem eq_2_4_not_mfcq {n m p : ℕ} (C : Constraints n m p)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible)
    (l : Fin m → ℝ) (u : Fin p → ℝ) (hu : ∀ j, 0 ≤ u j) (hcomp : ∀ j, C.g j xs ≠ 0 → u j = 0)
    (hnorm : max ‖l‖ ‖u‖ = 1)
    (h24 : ∑ i, l i • gradient (C.h i) xs + ∑ j, u j • gradient (C.g j) xs = 0) :
    ¬ C.MFCQ xs := by sorry

end StrictCQ.Scaled
