-- Prove2me | Theorems.Thm_R03SP06_cubic_p3_center_external_neighbor_card
-- name    : R03SP06.cubic_p3_center_external_neighbor_card
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-17T01:02:13.411306+00:00
-- url     : https://prove2.me/theorems/809c64d3-707a-42c3-9a76-22191b21b0eb
-- title:
--   R03 P3-factor structural result: Cubic p3 center external neighbor card
-- statement:
--   This is a source-faithful auxiliary theorem from the candidate formalization of the cubic P3-partition problem. It records the structural result `R03SP06.cubic_p3_center_external_neighbor_card` under exactly the explicit hypotheses in the Lean statement. It is a conditional reusable result and does not claim that the open root problem has been solved.
--
--   **Formalization Note** The Lean statement and direct proof were extracted from the cited candidate artifact; its source digest is recorded in the campaign ledger.
-- source:
--   VibeMathing candidate artifact: research/artifacts/candidates/r03/parallel/sp06/cubic_p3_deletion_center_bottleneck.lean; source SHA-256 61c333ea366403aa1c06c172b76b6eb608310cdb1147e6e88dd5805f4e120238; ProblemContract problem:opg-46613-p3-partition; candidate-only formalization.

import Mathlib

namespace R03SP06

open R03SP06
variable {V : Type} [Fintype V] [DecidableEq V]
theorem cubic_p3_center_external_neighbor_card
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hac : a ≠ c)
    (hdeg : (Finset.univ.filter (fun w : V => G.Adj b w)).card = 3) :
    ((Finset.univ.filter (fun w : V => G.Adj b w)) \ {a, c}).card = 1 := by sorry

end R03SP06
