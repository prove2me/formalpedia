-- Prove2me | Theorems.Thm_QEC_Locality_caseDGeKPieceFamily_union_selected
-- name    : QEC.Locality.caseDGeKPieceFamily_union_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:46:41.026607+00:00
-- url     : https://prove2.me/theorems/f5eff8e0-db43-4a3a-bb61-03b21d070c94
-- title:
--   Locality: case DGe KPiece Family union selected
-- statement:
--   The selected subsystem is exactly the bad-qubit piece together with all edge strips.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2226-L2234
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2226-L2234

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive

theorem QEC.Locality.caseDGeKPieceFamily_union_selected {α : Type*} [DecidableEq α]
    (badQubits : FiniteSubsystem ι) (edgeStrips : α → FiniteSubsystem ι)
    (s : Finset α) :
    (familyUnionSubsystem (caseDGeKPieceFamily badQubits edgeStrips)
        (caseDGeKPieceIndices s)).selected =
      badQubits.selected ∪ s.biUnion fun a => (edgeStrips a).selected := by sorry
