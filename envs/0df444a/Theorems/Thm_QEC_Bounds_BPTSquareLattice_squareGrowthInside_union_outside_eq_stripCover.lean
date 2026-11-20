-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_squareGrowthInside_union_outside_eq_stripCover
-- name    : QEC.Bounds.BPTSquareLattice.squareGrowthInside_union_outside_eq_stripCover
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:23:21.26154+00:00
-- url     : https://prove2.me/theorems/ced0934e-0583-451c-a598-f318124d5eff
-- title:
--   BPTSquare Lattice: square Growth Inside union outside eq strip Cover
-- statement:
--   The finite `B` and `C` layers reconstruct their common strip cover exactly.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L252-L260
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L252-L260

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

theorem QEC.Bounds.BPTSquareLattice.squareGrowthInside_union_outside_eq_stripCover (L : BPTSquareLattice)
    (origin : Nat × Nat) (width margin : Nat) :
    L.squareGrowthInside origin width margin ∪ L.squareGrowthOutside origin width margin =
      L.squareBoundaryFrameStripCover origin width margin := by sorry
