-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_biUnion_squarePartitionBComponents_eq_squarePartitionB
-- name    : QEC.Bounds.BPTSquareLattice.biUnion_squarePartitionBComponents_eq_squarePartitionB
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:24:45.657501+00:00
-- url     : https://prove2.me/theorems/3668a15b-6db1-4b7c-8cfc-05e53c3ae93a
-- title:
--   BPTSquare Lattice: bi Union square Partition BComponents eq square Partition B
-- statement:
--   The actual finite family of `B` blocks covers exactly the constructed `B` region.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L931-L958
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L931-L958

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

theorem QEC.Bounds.BPTSquareLattice.biUnion_squarePartitionBComponents_eq_squarePartitionB
    (L : BPTSquareLattice) {blockWidth : Nat} (hblockWidth : 0 < blockWidth)
    (margin : Nat) :
    (L.squarePartitionBComponents blockWidth margin).biUnion id =
      L.squarePartitionB blockWidth margin := by sorry
