-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_CoordinateRangeSeparated_symm
-- name    : QEC.Bounds.BPTSquareLattice.CoordinateRangeSeparated.symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:18:02.104738+00:00
-- url     : https://prove2.me/theorems/d8b1f259-5646-4823-90aa-dbe06db6ba51
-- title:
--   Coordinate Range Separated: symm
-- statement:
--   Coordinate-range separation is symmetric in its two finite regions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L513-L522
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L513-L522

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

theorem QEC.Bounds.BPTSquareLattice.CoordinateRangeSeparated.symm (L : BPTSquareLattice) {range : Nat}
    {left right : Finset L.Site}
    (hgap : L.CoordinateRangeSeparated range left right) :
    L.CoordinateRangeSeparated range right left := by sorry
