-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiRectangle_of_low_counter_clipped_growth
-- name    : QEC.Locality.exists_erasureRecovery_daiLiRectangle_of_low_counter_clipped_growth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:15:39.274503+00:00
-- url     : https://prove2.me/theorems/18e2bb62-532a-433e-a0fe-362890034032
-- title:
--   Locality: exists erasure Recovery dai Li Rectangle of low counter clipped growth
-- statement:
--   A low-interaction #496 rectangle has an actual CPTP recovery through the
--   same clipped rectangle-growth construction.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2042-L2088
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2042-L2088

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

theorem QEC.Locality.exists_erasureRecovery_daiLiRectangle_of_low_counter_clipped_growth
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold : ℝ) (lower upper : ℝ × ℝ)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hThreshold : 1 ≤ threshold)
    (hBaseHorizontal : baseHorizontalRadius ≤
      daiLiRectangleHorizontalRadius lower upper)
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
    (hLowCounter : 10 * regionInteractionCounter P embedding threshold
      (embedding.qubitsInRectangle lower upper) ≤ d)
    (hBoundaryBudget :
      48 * (daiLiRectangleHorizontalRadius lower upper +
        daiLiRectangleVerticalRadius lower upper + threshold) * threshold +
        (d : ℝ) / 10 < d) :
    ∃ recovery : QuantumChannel
        (daiLiRectangleSubsystem embedding lower upper).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiRectangleSubsystem embedding lower upper).complementSystem
        P.semanticCode
        (daiLiRectangleSubsystem embedding lower upper).erasureChannelFromRegister
          recovery := by sorry
