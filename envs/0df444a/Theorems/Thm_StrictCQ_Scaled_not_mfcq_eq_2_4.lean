-- Prove2me | Theorems.Thm_StrictCQ_Scaled_not_mfcq_eq_2_4
-- name    : StrictCQ.Scaled.not_mfcq_eq_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:57:42.514763+00:00
-- url     : https://prove2.me/theorems/ecf8e951-5766-462e-9d2d-0381f87810b1
-- title:
--   §2, p. 4 — failure of MFCQ gives a nonzero solution of (2.4)
-- statement:
--   Let $h_1,\dots,h_m$, $g_1,\dots,g_p$ be a constraint system on $\mathbb R^n$ and $x^*$ a feasible point at which the Mangasarian–Fromovitz constraint qualification fails. Then there exist $\lambda \in \mathbb R^m$ and $\mu \in \mathbb R^p$ with $\mu_j \ge 0$ for all $j$, $\mu_j = 0$ whenever $g_j(x^*) \ne 0$, and $\max\{\|\lambda\|_\infty, \|\mu\|_\infty\} = 1$ such that
--
--   $$
--   \sum_{i=1}^m \lambda_i \nabla h_i(x^*) + \sum_{j:\, g_j(x^*) = 0} \mu_j \nabla g_j(x^*) = 0 .
--   $$
--
--   This is the converse of the previous milestone, the theorem of the alternative behind the second half of §2: a point violating (2.3) violates MFCQ, hence admits a normalized nonzero solution of (2.4).
--
--   **Formalization Note** The page writes $\max\{\|\lambda\|_\infty, \|\mu^k\|_\infty\} = 1$; the superscript $k$ is a typo, and the statement uses $\|\mu\|_\infty$.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 4, §2 (second paragraph of the proof that (2.3) is the weakest)

import Mathlib
import Definitions.Def_StrictCQ_Scaled_Setting
import Definitions.Def_StrictCQ_Scaled_Conditions

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.Scaled

theorem not_mfcq_eq_2_4 {n m p : ℕ} (C : Constraints n m p)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible) (hnot : ¬ C.MFCQ xs) :
    ∃ (l : Fin m → ℝ) (u : Fin p → ℝ), (∀ j, 0 ≤ u j) ∧ (∀ j, C.g j xs ≠ 0 → u j = 0) ∧
      max ‖l‖ ‖u‖ = 1 ∧
      ∑ i, l i • gradient (C.h i) xs + ∑ j, u j • gradient (C.g j) xs = 0 := by sorry

end StrictCQ.Scaled
