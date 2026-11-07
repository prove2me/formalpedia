-- Prove2me | Theorems.Thm_QEC_Locality_exceptionalBad_separated_from_gridSideStrip
-- name    : QEC.Locality.exceptionalBad_separated_from_gridSideStrip
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:18:23.122565+00:00
-- url     : https://prove2.me/theorems/0fe47861-897a-4e65-abc7-1e609fb13118
-- title:
--   Locality: exceptional Bad separated from grid Side Strip
-- statement:
--   The finite geometric form of DL24's `B_0 \u2212 B'` separation argument.  A
--   point of `B_0` cannot be closer than `ell` to an actual width-`ell` side
--   strip: a shorter segment would place it in the periodic width-`2 * ell`
--   buffer, contradicting the preceding B'-to-C routing theorem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L342-L466
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L342-L466

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Metric
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
attribute [local instance] QEC.Locality.instClassicalDecidableDGeK

theorem QEC.Locality.exceptionalBad_separated_from_gridSideStrip
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (hw : 0 < w)
    (p q : ι) (side : DaiLiGridSideIndex)
    (hp : p ∈ daiLiDGeKExceptionalBadQubits P embedding threshold w ell t)
    (hq : q ∈ daiLiGridSideStripQubits embedding w ell (2 * ell)
      (gridOrigin w t) side) :
    ell ≤ embedding.distance p q := by sorry
