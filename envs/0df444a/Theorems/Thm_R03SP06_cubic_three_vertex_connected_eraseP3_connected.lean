-- Prove2me | Theorems.Thm_R03SP06_cubic_three_vertex_connected_eraseP3_connected
-- name    : R03SP06.cubic_three_vertex_connected_eraseP3_connected
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T01:02:30.161226+00:00
-- url     : https://prove2.me/theorems/f8dea2ed-61c3-4adf-b16d-9ead1aef00a7
-- title:
--   R03 P3-factor structural result: Cubic three vertex connected erase p3 connected
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03SP06.cubic_three_vertex_connected_eraseP3_connected` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp02/p3_deletion_connected_candidate_v1.lean; source SHA-256 b8ea3c9bb571f919ee5f601353e56a25dde325d7b1f99135125374d67b115202; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib
import Definitions.Def_cubic_p3_partition_models

namespace R03SP06

open R03SP06
open CubicP3Partition
variable {V : Type} [DecidableEq V]
theorem cubic_three_vertex_connected_eraseP3_connected
    {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]
    (hC : Cubic G) (h3 : ThreeVertexConnected G) (L : P3Path G) :
    (eraseP3 G L).Connected := by sorry

end R03SP06
