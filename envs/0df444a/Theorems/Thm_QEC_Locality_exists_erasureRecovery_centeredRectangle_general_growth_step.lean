-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_centeredRectangle_general_growth_step
-- name    : QEC.Locality.exists_erasureRecovery_centeredRectangle_general_growth_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:04:39.775881+00:00
-- url     : https://prove2.me/theorems/5254cca0-0147-441d-a516-43555e05833f
-- title:
--   Locality: exists erasure Recovery centered Rectangle general growth step
-- statement:
--   One actual rectangle-growth step with independently moving half-sides.
--   It constructs the boundary recovery from semantic distance, applies #377 to
--   the exact fixed-generator outer boundary, then applies #373 to the target
--   rectangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1343-L1422
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1343-L1422

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
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
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive

theorem QEC.Locality.exists_erasureRecovery_centeredRectangle_general_growth_step
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (center : ℝ × ℝ)
    (innerHorizontalRadius innerVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ)
    (hThreshold : 1 ≤ threshold)
    (hOuterHorizontal : 1 ≤ 2 * outerHorizontalRadius)
    (hOuterVertical : 1 ≤ 2 * outerVerticalRadius)
    (hHorizontal : innerHorizontalRadius ≤ outerHorizontalRadius)
    (hVertical : innerVerticalRadius ≤ outerVerticalRadius)
    (hHorizontalInset : outerHorizontalRadius - threshold ≤ innerHorizontalRadius)
    (hVerticalInset : outerVerticalRadius - threshold ≤ innerVerticalRadius)
    (hBoundarySmall :
      48 * (outerHorizontalRadius + outerVerticalRadius + threshold) * threshold +
        ((∑ q ∈ centeredRectangleQubits embedding center
          innerHorizontalRadius innerVerticalRadius,
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) < d)
    (hRecoveryInner :
      ∃ recovery : QuantumChannel
          (centeredRectangleSubsystem embedding center innerHorizontalRadius
            innerVerticalRadius).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (centeredRectangleSubsystem embedding center innerHorizontalRadius
            innerVerticalRadius).complementSystem
          P.semanticCode
          (centeredRectangleSubsystem embedding center innerHorizontalRadius
            innerVerticalRadius).erasureChannelFromRegister recovery) :
    ∃ recovery : QuantumChannel
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).complementSystem
        P.semanticCode
        (centeredRectangleSubsystem embedding center outerHorizontalRadius
          outerVerticalRadius).erasureChannelFromRegister recovery := by sorry
