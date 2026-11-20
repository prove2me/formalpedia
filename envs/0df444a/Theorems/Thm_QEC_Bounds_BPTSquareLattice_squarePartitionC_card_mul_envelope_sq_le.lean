-- Prove2me | Theorems.Thm_QEC_Bounds_BPTSquareLattice_squarePartitionC_card_mul_envelope_sq_le
-- name    : QEC.Bounds.BPTSquareLattice.squarePartitionC_card_mul_envelope_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T08:27:12.640649+00:00
-- url     : https://prove2.me/theorems/17dee4b9-b5c8-46a8-8711-0a54a1c785e0
-- title:
--   BPTSquare Lattice: square Partition C card mul envelope sq le
-- statement:
--   The regular core tiling gives the exact finite C bound after restoring the
--   envelope scale: `|C| * R^2 <= 16 w^2 n`. No boundary remainder is hidden.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2905-L2932
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/GeometricLocalityTradeoff/SquarePartition.lean#L2905-L2932

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

theorem QEC.Bounds.BPTSquareLattice.squarePartitionC_card_mul_envelope_sq_le
    (L : BPTSquareLattice) {blockWidth margin envelopeWidth tileRows tileColumns : Nat}
    (hblockWidth : 0 < blockWidth) (hseparationWidth : margin + margin ≤ blockWidth)
    (henvelope : blockWidth + margin + margin = envelopeWidth)
    (hrows : L.rows = tileRows * blockWidth)
    (hcolumns : L.columns = tileColumns * blockWidth) :
    (L.squarePartitionC blockWidth margin).card * (envelopeWidth * envelopeWidth) ≤
      16 * margin * margin * L.siteCount := by sorry
