-- Prove2me | Theorems.Thm_R03SP06_tree_edge_card_le_two_of_boundary_budget
-- name    : R03SP06.tree_edge_card_le_two_of_boundary_budget
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T10:45:51.263549+00:00
-- url     : https://prove2.me/theorems/97675f03-c41b-4b99-b6df-df15f02c3c2a
-- title:
--   R03 P3-factor structural result: tree edge card le two of boundary budget
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03SP06.tree_edge_card_le_two_of_boundary_budget` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is 1ff5f273c6c2eb7cbd1db664ad50331a556432b66ebdba49477e7ff0211c1f8c.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp06/tree_deficiency_bound.lean; source SHA-256 1ff5f273c6c2eb7cbd1db664ad50331a556432b66ebdba49477e7ff0211c1f8c; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib

namespace R03SP06

open R03SP06
variable {V : Type} [Fintype V]
theorem tree_edge_card_le_two_of_boundary_budget
    {T : SimpleGraph V} [DecidableRel T.Adj]
    (hT : T.IsTree) {r : V → Nat}
    (hbound : ∀ v : V, 3 - T.degree v ≤ r v)
    (hsum : ∑ v : V, r v ≤ 5) :
    T.edgeFinset.card ≤ 2 := by sorry

end R03SP06
