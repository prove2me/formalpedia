-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiRectangle_of_piece_alternative
-- name    : QEC.Locality.exists_erasureRecovery_daiLiRectangle_of_piece_alternative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:15:37.751977+00:00
-- url     : https://prove2.me/theorems/4d6625e4-18bd-409d-a1a8-2b1867fa4300
-- title:
--   Locality: exists erasure Recovery dai Li Rectangle of piece alternative
-- statement:
--   A true #496 subdivision rectangle is correctable in either branch of its
--   proved local contract: low interaction count uses clipped growth, while a
--   short horizontal band uses the packing-to-distance route.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2120-L2175
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2120-L2175

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
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
attribute [local instance] QEC.Locality.instClassicalDecidableCorrectable

theorem QEC.Locality.exists_erasureRecovery_daiLiRectangle_of_piece_alternative
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold ell w : ℝ) (lower upper : ℝ × ℝ)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hThreshold : 1 ≤ threshold)
    (hBaseHorizontal : baseHorizontalRadius ≤ daiLiRectangleHorizontalRadius lower upper)
    (hBaseVertical : baseVerticalRadius ≤ daiLiRectangleVerticalRadius lower upper)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : daiLiRectangleHorizontalRadius lower upper ≤
      baseHorizontalRadius + steps * threshold)
    (hReachVertical : daiLiRectangleVerticalRadius lower upper ≤
      baseVerticalRadius + steps * threshold)
    (hBaseCard : (centeredRectangleQubits embedding
      (daiLiRectangleCenter lower upper) baseHorizontalRadius
      baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (daiLiRectangleHorizontalRadius lower upper +
        daiLiRectangleVerticalRadius lower upper + threshold) * threshold +
        (d : ℝ) / 10 < d)
    (hSpan : upper.1 - lower.1 = w) (hWidth : 1 ≤ w) (hEll : 1 ≤ ell)
    (hMinimumHeight : 5 * ell ≤ upper.2 - lower.2)
    (hShortPackingScale : 60 * w * ell < d)
    (hPiece : 10 * regionInteractionCounter P embedding threshold
        (embedding.qubitsInRectangle lower upper) ≤ d ∨
      upper.2 - lower.2 ≤ 10 * ell) :
    ∃ recovery : QuantumChannel
        (daiLiRectangleSubsystem embedding lower upper).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiRectangleSubsystem embedding lower upper).complementSystem
        P.semanticCode
        (daiLiRectangleSubsystem embedding lower upper).erasureChannelFromRegister recovery := by sorry
