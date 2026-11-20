-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_squarePartitionC_card_mul_envelope_sq_le_of_regularSquare
-- name    : QEC.Bounds.BPTSquareLattice.squarePartitionC_card_mul_envelope_sq_le_of_regularSquare
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:26:37.245534+00:00
-- url     : https://prove2.me/theorems/1bdaac2f-f38d-42b3-be65-7972bb52a2d9
-- title:
--   BPTSquare Lattice: square Partition C card mul envelope sq le of regular Square
-- statement:
--   For the source's regular open square lattice, clipped final tiles preserve the
--   finite BPT corner estimate.  No block-width divisibility is required: the
--   last tile in each direction is included in the proved quotient count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2939-L2986
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2939-L2986

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

theorem QEC.Bounds.BPTSquareLattice.squarePartitionC_card_mul_envelope_sq_le_of_regularSquare
    (L : BPTSquareLattice) {blockWidth margin envelopeWidth : Nat}
    (hblockWidth : 0 < blockWidth) (hmargin : margin + margin ≤ blockWidth)
    (henvelope : blockWidth + margin + margin = envelopeWidth)
    (hregular : L.rows = L.columns) (hblockLeSide : blockWidth ≤ L.rows) :
    (L.squarePartitionC blockWidth margin).card * (envelopeWidth * envelopeWidth) ≤
      64 * margin * margin * L.siteCount := by sorry
