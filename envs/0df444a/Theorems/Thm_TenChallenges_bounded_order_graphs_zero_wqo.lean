-- Prove2me | Theorems.Thm_TenChallenges_bounded_order_graphs_zero_wqo
-- name    : TenChallenges.bounded_order_graphs_zero_wqo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:19:34.295882+00:00
-- url     : https://prove2.me/theorems/dfdac665-81fb-46cd-996d-7d2b25f2facc
-- title:
--   Better-quasi-ordering by graph minors: Level zero for graphs of bounded order
-- statement:
--   For each N, simple graphs represented on vertex sets Fin n with n≤N are well-quasi-ordered by the minor relation at ordinal level zero. This bounded-order case does not assert the graph-minor theorem for unbounded orders.
-- source:
--   Elementary special case / supporting lemma for Challenge 06. Definitions: https://tenchallenges.github.io/ten-challenges/#problems

import Definitions.Def_TenChallenges_Challenge_06
import Mathlib.Data.Fintype.Pigeonhole
universe u

theorem TenChallenges.bounded_order_graphs_zero_wqo (N : ℕ) :
    IsAlphaWQO (fun G H : (Σ n : Fin (N + 1), SimpleGraph (Fin n.val)) =>
      Nonempty (SimpleGraph.Minor G.2 H.2)) 0 := by sorry
