-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_squareInnerCore_subset_outerSquare
-- name    : QEC.Bounds.BPTSquareLattice.squareInnerCore_subset_outerSquare
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:28:46.250282+00:00
-- url     : https://prove2.me/theorems/87b7e86a-f8bc-4184-8b11-e20261399a47
-- title:
--   BPTSquare Lattice: square Inner Core subset outer Square
-- statement:
--   The deep core is contained in the visible outer square whenever it is nonempty.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L165-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L165-L180

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

theorem QEC.Bounds.BPTSquareLattice.squareInnerCore_subset_outerSquare (L : BPTSquareLattice)
    (origin : Nat × Nat) (width margin : Nat) (hwidth : margin + margin ≤ width) :
    L.squareInnerCore origin width margin ⊆
      L.square (origin.1 - margin, origin.2 - margin) (width + margin + margin) := by sorry
