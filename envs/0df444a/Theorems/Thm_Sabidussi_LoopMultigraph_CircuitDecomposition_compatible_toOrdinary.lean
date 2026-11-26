-- Prove2me | Theorems.Thm_Sabidussi_LoopMultigraph_CircuitDecomposition_compatible_toOrdinary
-- name    : Sabidussi.LoopMultigraph.CircuitDecomposition.compatible_toOrdinary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:11:38.51982+00:00
-- url     : https://prove2.me/theorems/90a47187-cb38-5697-a158-7489c0968968
-- title:
--   Circuit Decomposition: compatible to Ordinary
-- statement:
--   The Circuit Decomposition construction uses the compatible to Ordinary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OrdinaryCircuit.lean#L410-L416
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/OrdinaryCircuit.lean#L410-L416

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

theorem Sabidussi.LoopMultigraph.CircuitDecomposition.compatible_toOrdinary {T : G.EulerTour}
    {S : G.CircuitDecomposition} (h : S.Compatible T) : S.toOrdinary.Compatible T := by sorry
