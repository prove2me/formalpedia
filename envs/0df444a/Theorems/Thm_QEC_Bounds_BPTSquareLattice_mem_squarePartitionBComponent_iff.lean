-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_mem_squarePartitionBComponent_iff
-- name    : QEC.Bounds.BPTSquareLattice.mem_squarePartitionBComponent_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:20:28.173314+00:00
-- url     : https://prove2.me/theorems/63f3e0a2-757f-45c1-9949-9740c902701b
-- title:
--   BPTSquare Lattice: mem square Partition BComponent iff
-- statement:
--   Membership in an indexed `B` block exposes both its tile and source color.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L424-L429
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L424-L429

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

theorem QEC.Bounds.BPTSquareLattice.mem_squarePartitionBComponent_iff (L : BPTSquareLattice)
    (blockWidth margin : Nat) (index : Nat × Nat) (site : L.Site) :
    site ∈ L.squarePartitionBComponent blockWidth margin index ↔
      site ∈ L.tile blockWidth index ∧ ¬ L.cornerCutout blockWidth margin site ∧
        ¬ L.checkerboardEven blockWidth site := by sorry
