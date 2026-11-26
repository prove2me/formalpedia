-- Prove2me | Theorems.Thm_Sabidussi_LoopMultigraph_CompatibleFourColoring_exists_compatible_circuit_decomposition
-- name    : Sabidussi.LoopMultigraph.CompatibleFourColoring.exists_compatible_circuit_decomposition
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:11:21.040603+00:00
-- url     : https://prove2.me/theorems/8107b7d3-17dd-514b-af19-f3304c96424f
-- title:
--   Compatible Four Coloring: exists compatible circuit decomposition
-- statement:
--   Every compatible four-colouring yields a compatible circuit decomposition.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LoopMultigraph.lean#L270-L313
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/LoopMultigraph.lean#L270-L313

import Definitions.Def_Sabidussi_Color
import Definitions.Def_Sabidussi_Statement
import Mathlib.Data.Fin.Rev
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finite.Set
import Mathlib.Data.Fintype.Sets
import Definitions.Def_Sabidussi_LoopMultigraph
set_option autoImplicit true
open Sabidussi
open scoped BigOperators
open Sabidussi.LoopMultigraph
variable {V E : Type*} [Fintype V] [Fintype E]
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)
open Sabidussi
variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (G : LoopMultigraph V E)
open Sabidussi.LoopMultigraph.CompatibleFourColoring

theorem Sabidussi.LoopMultigraph.CompatibleFourColoring.exists_compatible_circuit_decomposition
    {T : G.EulerTour} (K : G.CompatibleFourColoring T) :
    ∃ S : G.CircuitDecomposition, S.Compatible T := by sorry
