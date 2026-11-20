-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_squareBoundaryFrameStripCover_card_le_sixteen_mul
-- name    : QEC.Bounds.BPTSquareLattice.squareBoundaryFrameStripCover_card_le_sixteen_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:21:06.183655+00:00
-- url     : https://prove2.me/theorems/c10f8092-e6da-4a24-a920-7769c016d674
-- title:
--   BPTSquare Lattice: square Boundary Frame Strip Cover card le sixteen mul
-- statement:
--   The four source-width strips have at most `16 * w * R` sites when `R >= 2w`.
--   This is an open-boundary estimate: clipped strips only lose sites, and no
--   periodic or implicit infinite-lattice convention is used.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L187-L249
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L187-L249

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

theorem QEC.Bounds.BPTSquareLattice.squareBoundaryFrameStripCover_card_le_sixteen_mul (L : BPTSquareLattice)
    (origin : Nat × Nat) (width margin : Nat) (hwidth : margin + margin ≤ width) :
    (L.squareBoundaryFrameStripCover origin width margin).card ≤ 16 * margin * width := by sorry
