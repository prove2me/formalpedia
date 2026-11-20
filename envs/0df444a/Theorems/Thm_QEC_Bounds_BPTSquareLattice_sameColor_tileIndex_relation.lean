-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_sameColor_tileIndex_relation
-- name    : QEC.Bounds.BPTSquareLattice.sameColor_tileIndex_relation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:22:59.12419+00:00
-- url     : https://prove2.me/theorems/9d12b3e3-123d-461a-937f-42e3bea5d255
-- title:
--   BPTSquare Lattice: same Color tile Index relation
-- statement:
--   Two distinct checkerboard indices are either separated by a whole tile in one
--   coordinate or are diagonal neighbours.  The one-axis-neighbour cases are
--   excluded by the common parity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L712-L750
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L712-L750

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

theorem QEC.Bounds.BPTSquareLattice.sameColor_tileIndex_relation (parityOffset : Nat) (left right : Nat × Nat)
    (hevenLeft : Even (left.1 + left.2 + parityOffset))
    (hevenRight : Even (right.1 + right.2 + parityOffset))
    (hne : left ≠ right) :
    left.1 + 1 < right.1 ∨ right.1 + 1 < left.1 ∨
      left.2 + 1 < right.2 ∨ right.2 + 1 < left.2 ∨
        (right.1 = left.1 + 1 ∧ right.2 = left.2 + 1) ∨
          (right.1 = left.1 + 1 ∧ left.2 = right.2 + 1) ∨
            (left.1 = right.1 + 1 ∧ right.2 = left.2 + 1) ∨
              left.1 = right.1 + 1 ∧ left.2 = right.2 + 1 := by sorry
