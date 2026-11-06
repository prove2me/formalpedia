-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_square_growth_step
-- name    : QEC.Locality.exists_erasureRecovery_square_growth_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:03:41.450199+00:00
-- url     : https://prove2.me/theorems/ca86a3ec-cc16-4c33-8659-df45de77d92e
-- title:
--   Locality: exists erasure Recovery square growth step
-- statement:
--   One source-faithful growing-square step.  Semantic distance corrects the
--   computed shell/crossing boundary, #377 expands an already-correctable inner
--   square across that actual boundary, and #373 shrinks the union to the concrete
--   outer square.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L423-L484
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L423-L484

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

theorem QEC.Locality.exists_erasureRecovery_square_growth_step
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (center : ℝ × ℝ) (outerRadius threshold : ℝ)
    (hthreshold : 1 ≤ threshold) (hdiameter : 1 ≤ 2 * outerRadius)
    (hBoundarySmall :
      48 * outerRadius * threshold +
          ((∑ q ∈ squareQubits embedding center (outerRadius - threshold),
            P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) < d)
    (hRecoveryInner :
      ∃ recovery : QuantumChannel
          (squareSubsystem embedding center
            (outerRadius - threshold)).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (squareSubsystem embedding center
            (outerRadius - threshold)).complementSystem
          P.semanticCode
          (squareSubsystem embedding center
            (outerRadius - threshold)).erasureChannelFromRegister recovery) :
    ∃ recovery : QuantumChannel
        (squareSubsystem embedding center outerRadius).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (squareSubsystem embedding center outerRadius).complementSystem
        P.semanticCode
        (squareSubsystem embedding center outerRadius).erasureChannelFromRegister recovery := by sorry
