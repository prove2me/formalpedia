-- Prove2me | Theorems.Thm_Sabidussi_LoopMultigraph_loop_sabidussi_compatibility_ordinary
-- name    : Sabidussi.LoopMultigraph.loop_sabidussi_compatibility_ordinary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:11:43.369259+00:00
-- url     : https://prove2.me/theorems/7c2744d8-e0c0-5216-a875-8ceb42de226b
-- title:
--   Loop Multigraph: loop sabidussi compatibility ordinary
-- statement:
--   Sabidussi compatibility with the conclusion expressed using ordinary connected 2-regular
--   circuits rather than minimal binary-even edge sets.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OrdinaryCircuit.lean#L420-L424
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OrdinaryCircuit.lean#L420-L424

import Definitions.Def_Sabidussi_LoopGraphBridge
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_Sabidussi_OrdinaryCircuit
set_option autoImplicit true
open Sabidussi
open Sabidussi.LoopMultigraph
open scoped BigOperators
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)

theorem Sabidussi.LoopMultigraph.loop_sabidussi_compatibility_ordinary {G : LoopMultigraph V E} (T : G.EulerTour)
    (hmin : ∀ v : V, 4 ≤ G.degree v) :
    ∃ S : G.OrdinaryCircuitDecomposition, S.Compatible T := by sorry
