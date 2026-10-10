-- Prove2me | Theorems.Thm_StrictCQ_CAKKT_theorem_4_3
-- name    : StrictCQ.CAKKT.theorem_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:33:14.911532+00:00
-- url     : https://prove2.me/theorems/059c8a4a-52d3-40f6-b5ac-c1ceadce6cca
-- title:
--   Theorem 4.3, p. 9 — CAKKT-regularity is the weakest strict constraint qualification associated with CAKKT
-- statement:
--   Let $h_i,g_j$ be continuously differentiable and let $x^*$ be feasible for (1.1). Then $x^*$ is CAKKT-regular if and only if, for every continuously differentiable objective $f$,
--   $$\text{CAKKT holds at } x^* \text{ for } f\ \Longrightarrow\ \text{KKT holds at } x^* \text{ for } f.$$
--
--   The forward direction says that CAKKT-regularity is a strict constraint qualification for CAKKT; the backward direction says that any condition on the constraints with this property implies CAKKT-regularity, so CAKKT-regularity is the weakest one.
--
--   **Formalization Note** The objective is quantified inside the equivalence, for fixed constraints and fixed $x^*$. KKT is in multiplier form with sign and complementarity conditions; CAKKT includes $x^k\to x^*$.
-- source:
--   Andreani, Martínez, Ramos & Silva, Strict constraint qualifications and sequential optimality conditions for constrained optimization, Optimization Online 5197 (version of November 12, 2015), p. 9, Theorem 4.3

import Mathlib
import Definitions.Def_StrictCQ_CAKKT_Setting
import Definitions.Def_StrictCQ_CAKKT_Conditions

open Filter Topology
open scoped InnerProductSpace

namespace StrictCQ.CAKKT

theorem theorem_4_3 {n m p : ℕ} (C : Constraints n m p) (hC : C.IsC1)
    {xs : EuclideanSpace ℝ (Fin n)} (hxs : xs ∈ C.feasible) :
    C.CAKKTRegular xs ↔
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f → C.IsCAKKT f xs → C.IsKKT f xs := by sorry
end StrictCQ.CAKKT
