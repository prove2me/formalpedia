-- Prove2me | Theorems.Thm_StrictCQ_Scaled_activeCone_univ_kkt
-- name    : StrictCQ.Scaled.activeCone_univ_kkt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:58:20.451199+00:00
-- url     : https://prove2.me/theorems/b0ae48a6-dc96-4f32-b22d-75b902b072dc
-- title:
--   §2, p. 3 — if the cone of active gradients is ℝⁿ, KKT holds for every objective
-- statement:
--   Let $h_1,\dots,h_m$, $g_1,\dots,g_p$ be a constraint system on $\mathbb R^n$ and $x^*$ a feasible point. Suppose the cone of active gradients is the whole space:
--
--   $$
--   \Big\{\sum_{i=1}^m \lambda_i \nabla h_i(x^*) + \sum_{j:\, g_j(x^*) = 0} \mu_j \nabla g_j(x^*) : \lambda \in \mathbb R^m,\ \mu_j \ge 0\Big\} = \mathbb R^n .
--   $$
--
--   Then for every function $f : \mathbb R^n \to \mathbb R$, the point $x^*$ satisfies the KKT conditions for $f$.
--
--   This is the first half of the proof that (2.3) is a strict constraint qualification for Scaled-AKKT: when the cone is full, KKT holds independently of the objective function.
--
--   **Formalization Note** No differentiability of $f$ is assumed: the statement uses only the vector $\nabla f(x^*)$, which Mathlib's `gradient` returns for any function.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 3, §2 (paragraph after (2.3))

import Mathlib
import Definitions.Def_StrictCQ_Scaled_Setting
import Definitions.Def_StrictCQ_Scaled_Conditions

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.Scaled

theorem activeCone_univ_kkt {n m p : ℕ} (C : Constraints n m p)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible)
    (hcone : C.activeCone xs = Set.univ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    C.IsKKT f xs := by sorry

end StrictCQ.Scaled
