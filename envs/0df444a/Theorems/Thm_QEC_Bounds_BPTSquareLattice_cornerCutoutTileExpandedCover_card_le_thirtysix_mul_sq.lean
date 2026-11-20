-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_cornerCutoutTileExpandedCover_card_le_thirtysix_mul_sq
-- name    : QEC.Bounds.BPTSquareLattice.cornerCutoutTileExpandedCover_card_le_thirtysix_mul_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:25:16.397789+00:00
-- url     : https://prove2.me/theorems/f96afdac-69a2-44fc-8348-73de0f180d78
-- title:
--   BPTSquare Lattice: corner Cutout Tile Expanded Cover card le thirtysix mul sq
-- statement:
--   The four enlarged C corner squares have at most `36 * margin^2` sites.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1365-L1433
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L1365-L1433

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

theorem QEC.Bounds.BPTSquareLattice.cornerCutoutTileExpandedCover_card_le_thirtysix_mul_sq (L : BPTSquareLattice)
    (blockWidth margin : Nat) (index : Nat × Nat) :
    (L.cornerCutoutTileExpandedCover blockWidth margin index).card ≤
      36 * margin * margin := by sorry
