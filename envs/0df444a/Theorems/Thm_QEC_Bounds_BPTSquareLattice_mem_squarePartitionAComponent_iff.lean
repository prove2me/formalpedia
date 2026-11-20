-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_mem_squarePartitionAComponent_iff
-- name    : QEC.Bounds.BPTSquareLattice.mem_squarePartitionAComponent_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:21:19.999643+00:00
-- url     : https://prove2.me/theorems/a52eb25f-dcfe-4f30-9075-04ed4c6cbfa2
-- title:
--   BPTSquare Lattice: mem square Partition AComponent iff
-- statement:
--   Membership in an indexed `A` block exposes both its tile and source color.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L416-L421
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L416-L421

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open Semantics
universe u v
open QEC.Bounds.BPTSquareLattice

theorem QEC.Bounds.BPTSquareLattice.mem_squarePartitionAComponent_iff (L : BPTSquareLattice)
    (blockWidth margin : Nat) (index : Nat × Nat) (site : L.Site) :
    site ∈ L.squarePartitionAComponent blockWidth margin index ↔
      site ∈ L.tile blockWidth index ∧ ¬ L.cornerCutout blockWidth margin site ∧
        L.checkerboardEven blockWidth site := by sorry
