-- Prove2me | Theorems.Thm_Sabidussi_LoopMultigraph_loop_sabidussi_compatibility
-- name    : Sabidussi.LoopMultigraph.loop_sabidussi_compatibility
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:11:17.190798+00:00
-- url     : https://prove2.me/theorems/1366862e-30bb-5a4a-bd8f-f7c5167ce496
-- title:
--   Loop Multigraph: loop sabidussi compatibility
-- statement:
--   Sabidussi compatibility for finite endpoint multigraphs, including loops.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LoopGraphBridge.lean#L113-L124
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LoopGraphBridge.lean#L113-L124

import Definitions.Def_Sabidussi_LoopMultigraph
import Definitions.Def_Sabidussi_CyclicWord
import Definitions.Def_Sabidussi_LoopGraphBridge
set_option autoImplicit true
open Sabidussi
open Sabidussi.LoopMultigraph
open Sabidussi
open scoped BigOperators
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {G : LoopMultigraph V E}

theorem Sabidussi.LoopMultigraph.loop_sabidussi_compatibility (T : G.EulerTour)
    (hmin : ∀ v : V, 4 ≤ G.degree v) :
    ∃ S : G.CircuitDecomposition, S.Compatible T := by sorry
