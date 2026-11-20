-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_square_union_squareGrowthOutside_eq_grownSquare
-- name    : QEC.Bounds.BPTSquareLattice.square_union_squareGrowthOutside_eq_grownSquare
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:22:46.028065+00:00
-- url     : https://prove2.me/theorems/f4d553a5-9320-4fc7-b3db-fc38dafb05d7
-- title:
--   BPTSquare Lattice: square union square Growth Outside eq grown Square
-- statement:
--   The source growth layers around the inner square reconstruct the larger square.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L263-L274
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L263-L274

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

theorem QEC.Bounds.BPTSquareLattice.square_union_squareGrowthOutside_eq_grownSquare (L : BPTSquareLattice)
    (origin : Nat × Nat) (width margin : Nat) (hwidth : margin + margin ≤ width)
    (hmarginOrigin : margin ≤ origin.1 ∧ margin ≤ origin.2) :
    L.square origin width ∪ L.squareGrowthOutside origin width margin =
      L.square (origin.1 - margin, origin.2 - margin) (width + margin + margin) := by sorry
