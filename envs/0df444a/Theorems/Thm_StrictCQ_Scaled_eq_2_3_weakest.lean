-- Prove2me | Theorems.Thm_StrictCQ_Scaled_eq_2_3_weakest
-- name    : StrictCQ.Scaled.eq_2_3_weakest
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T20:58:01.128893+00:00
-- url     : https://prove2.me/theorems/14ae9d9a-77cb-4610-b1e2-73599178380d
-- title:
--   §2, (2.3), pp. 3–4 — MFCQ or a full active-gradient cone is the weakest strict CQ associated with Scaled-AKKT
-- statement:
--   Let $h_1,\dots,h_m$, $g_1,\dots,g_p : \mathbb R^n \to \mathbb R$ be continuously differentiable constraint functions and let $x^*$ be a feasible point: $h_i(x^*) = 0$ and $g_j(x^*) \le 0$ for all $i, j$. Then the following are equivalent:
--
--   1. condition (2.3) holds at $x^*$:
--   $$
--   \text{MFCQ holds at } x^* \quad\text{or}\quad \Big\{\sum_{i=1}^m \lambda_i \nabla h_i(x^*) + \sum_{j:\, g_j(x^*) = 0} \mu_j \nabla g_j(x^*) : \lambda \in \mathbb R^m,\ \mu_j \ge 0\Big\} = \mathbb R^n ;
--   $$
--   2. for every continuously differentiable objective $f : \mathbb R^n \to \mathbb R$, if the Scaled-AKKT condition holds at $x^*$ for $f$, then $x^*$ satisfies KKT for $f$.
--
--   The implication 1 ⇒ 2 says that (2.3) is a strict constraint qualification associated with Scaled-AKKT; the implication 2 ⇒ 1 says that every strict constraint qualification associated with Scaled-AKKT implies (2.3), so (2.3) is the weakest one. It is the motivating example of the paper for the analysis carried out later for AGP, CAKKT and SAKKT.
--
--   **Formalization Note** The constraint functions are assumed $C^1$, the paper's standing assumption ("continuous first derivatives"). The objective is quantified inside the equivalence, so the left side is a property of $h$, $g$ and $x^*$ only. "or" is inclusive, and the cone condition is equality of the cone with $\mathbb R^n$. KKT is in multiplier form with sign and complementarity conditions.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), pp. 3–4, §2, (2.3)

import Mathlib
import Definitions.Def_StrictCQ_Scaled_Setting
import Definitions.Def_StrictCQ_Scaled_Conditions

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.Scaled

theorem eq_2_3_weakest {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible) :
    (C.MFCQ xs ∨ C.activeCone xs = Set.univ) ↔
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f → C.ScaledAKKT f xs → C.IsKKT f xs := by sorry

end StrictCQ.Scaled
