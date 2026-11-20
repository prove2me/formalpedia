-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_siteCount_eq_rows_mul_columns
-- name    : QEC.Bounds.BPTSquareLattice.siteCount_eq_rows_mul_columns
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:23:10.56827+00:00
-- url     : https://prove2.me/theorems/17c8bc97-cc76-4533-a6ca-f16a1c8af8ef
-- title:
--   BPTSquare Lattice: site Count eq rows mul columns
-- statement:
--   The finite site count of a rectangular BPT lattice is its row-column product.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2897-L2899
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2897-L2899

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

theorem QEC.Bounds.BPTSquareLattice.siteCount_eq_rows_mul_columns (L : BPTSquareLattice) :
    L.siteCount = L.rows * L.columns := by sorry
