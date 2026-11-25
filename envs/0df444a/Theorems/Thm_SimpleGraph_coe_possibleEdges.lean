-- Prove2me | Theorems.Thm_SimpleGraph_coe_possibleEdges
-- name    : SimpleGraph.coe_possibleEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:01:28.368624+00:00
-- url     : https://prove2.me/theorems/02e780b3-afac-5698-858f-36263097e619
-- title:
--   Simple Graph: coe possible Edges
-- statement:
--   The possible edges are the non-diagonal elements of `Sym2 V`.
--
--   Source: https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/MeasureBridge.lean#L74-L77
-- source:
--   https://github.com/Egly443/lean-probabilistic-method/blob/841e3042ef057564ae3cbd2322e0f369bbf64d34/ProbabilisticMethod/MeasureBridge.lean#L74-L77

module
public import Definitions.Def_ProbabilisticMethod_RandomGraph
public import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
public import Definitions.Def_ProbabilisticMethod_MeasureBridge
set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory unitInterval
open scoped Finset
open SimpleGraph
variable {V : Type*}
variable [Fintype V] [DecidableEq V]

theorem SimpleGraph.coe_possibleEdges : (possibleEdges V : Set (Sym2 V)) = Sym2.diagSetᶜ := by sorry
