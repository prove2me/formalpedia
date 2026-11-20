-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_mem_rectangle_iff
-- name    : QEC.Bounds.BPTSquareLattice.mem_rectangle_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:20:45.535608+00:00
-- url     : https://prove2.me/theorems/9c41de58-c0ea-42b6-988f-17942e2de98c
-- title:
--   BPTSquare Lattice: mem rectangle iff
-- statement:
--   The BPTSquare Lattice construction uses the mem rectangle iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L68-L73
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L68-L73

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

theorem QEC.Bounds.BPTSquareLattice.mem_rectangle_iff (L : BPTSquareLattice) (origin : Nat × Nat)
    (rowWidth columnWidth : Nat) (site : L.Site) :
    site ∈ L.rectangle origin rowWidth columnWidth ↔
      origin.1 ≤ site.1.val ∧ site.1.val < origin.1 + rowWidth ∧
        origin.2 ≤ site.2.val ∧ site.2.val < origin.2 + columnWidth := by sorry
