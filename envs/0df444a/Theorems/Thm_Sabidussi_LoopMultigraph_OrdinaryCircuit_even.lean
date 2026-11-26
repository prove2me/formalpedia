-- Prove2me | Theorems.Thm_Sabidussi_LoopMultigraph_OrdinaryCircuit_even
-- name    : Sabidussi.LoopMultigraph.OrdinaryCircuit.even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:15:42.335474+00:00
-- url     : https://prove2.me/theorems/a10578e2-6db4-4822-926d-4494a8784030
-- title:
--   Ordinary Circuit: even
-- statement:
--   An ordinary circuit is an even edge set (including the singleton-loop case).
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OrdinaryCircuit.lean#L370-L381
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OrdinaryCircuit.lean#L370-L381

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

theorem Sabidussi.LoopMultigraph.OrdinaryCircuit.even (C : G.OrdinaryCircuit) : G.IsEvenEdgeSet C.edges := by sorry
