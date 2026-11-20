-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_CoordinateRangeSeparated_mono
-- name    : QEC.Bounds.BPTSquareLattice.CoordinateRangeSeparated.mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:22:52.840436+00:00
-- url     : https://prove2.me/theorems/455ec84f-b48f-4ff7-8647-27d206a668d7
-- title:
--   Coordinate Range Separated: mono
-- statement:
--   Coordinate separation is preserved when either region is shrunk.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L504-L510
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L504-L510

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

theorem QEC.Bounds.BPTSquareLattice.CoordinateRangeSeparated.mono (L : BPTSquareLattice) {range : Nat}
    {left' left right' right : Finset L.Site}
    (hgap : L.CoordinateRangeSeparated range left right) (hleft : left' ⊆ left)
    (hright : right' ⊆ right) :
    L.CoordinateRangeSeparated range left' right' := by sorry
