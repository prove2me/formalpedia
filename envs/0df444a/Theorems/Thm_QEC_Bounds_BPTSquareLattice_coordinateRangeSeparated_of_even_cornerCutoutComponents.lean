-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_coordinateRangeSeparated_of_even_cornerCutoutComponents
-- name    : QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_of_even_cornerCutoutComponents
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:20:45.358303+00:00
-- url     : https://prove2.me/theorems/caffb0ac-37e8-4b61-be27-7ada31d8299e
-- title:
--   BPTSquare Lattice: coordinate Range Separated of even corner Cutout Components
-- statement:
--   The full same-color separation proof for any family of corner-trimmed tile
--   components.  This combines the parity classification with the proven finite
--   row, column, and diagonal coordinate arguments.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L757-L821
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L757-L821

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

theorem QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_of_even_cornerCutoutComponents
    (L : BPTSquareLattice) {blockWidth margin range : Nat}
    (hblockWidth : 0 < blockWidth) (hrangeBlock : range ≤ blockWidth)
    (hrangeMargin : range ≤ margin) (component : Nat × Nat → Finset L.Site)
    (hcomponentTile : ∀ index, component index ⊆ L.tile blockWidth index)
    (hcomponentNotCorner : ∀ index site, site ∈ component index →
      ¬ L.cornerCutout blockWidth margin site)
    (parityOffset : Nat) (leftIndex rightIndex : Nat × Nat)
    (hevenLeft : Even (leftIndex.1 + leftIndex.2 + parityOffset))
    (hevenRight : Even (rightIndex.1 + rightIndex.2 + parityOffset))
    (hne : leftIndex ≠ rightIndex) :
    L.CoordinateRangeSeparated range (component leftIndex) (component rightIndex) := by sorry
