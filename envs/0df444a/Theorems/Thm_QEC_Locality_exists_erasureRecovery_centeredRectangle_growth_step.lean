-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_centeredRectangle_growth_step
-- name    : QEC.Locality.exists_erasureRecovery_centeredRectangle_growth_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:40:48.386228+00:00
-- url     : https://prove2.me/theorems/4d88442c-c3b7-4cb8-a638-d3fe72503d16
-- title:
--   Locality: exists erasure Recovery centered Rectangle growth step
-- statement:
--   One source-faithful actual rectangle-growth step.  The boundary recovery
--   comes from semantic distance, then #377 expands it over the concrete
--   fixed-generator boundary, and #373 restricts back to the target rectangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1004-L1073
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1004-L1073

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

theorem QEC.Locality.exists_erasureRecovery_centeredRectangle_growth_step
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (center : ℝ × ℝ) (outerHorizontalRadius outerVerticalRadius threshold : ℝ)
    (hthreshold : 1 ≤ threshold) (hHorizontal : 1 ≤ 2 * outerHorizontalRadius)
    (hVertical : 1 ≤ 2 * outerVerticalRadius)
    (hBoundarySmall :
      24 * (outerHorizontalRadius + outerVerticalRadius) * threshold +
          ((∑ q ∈ centeredRectangleQubits embedding center
            (outerHorizontalRadius - threshold) (outerVerticalRadius - threshold),
            P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) < d)
    (hRecoveryInner :
      ∃ recovery : QuantumChannel
          (centeredRectangleSubsystem embedding center
            (outerHorizontalRadius - threshold)
            (outerVerticalRadius - threshold)).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (centeredRectangleSubsystem embedding center
            (outerHorizontalRadius - threshold)
            (outerVerticalRadius - threshold)).complementSystem
          P.semanticCode
          (centeredRectangleSubsystem embedding center
            (outerHorizontalRadius - threshold)
            (outerVerticalRadius - threshold)).erasureChannelFromRegister recovery) :
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
