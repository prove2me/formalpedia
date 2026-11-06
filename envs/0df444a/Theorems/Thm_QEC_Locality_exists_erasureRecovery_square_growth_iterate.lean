-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_square_growth_iterate
-- name    : QEC.Locality.exists_erasureRecovery_square_growth_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:39:44.787813+00:00
-- url     : https://prove2.me/theorems/1e77e618-f9bd-4d67-9b48-194abe1f400a
-- title:
--   Locality: exists erasure Recovery square growth iterate
-- statement:
--   Finite recursion of the concrete growing-square step.  The indexed budget is
--   checked at every actual radius; no raw partition or prepackaged correctability
--   field is accepted.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L507-L556
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L507-L556

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

theorem QEC.Locality.exists_erasureRecovery_square_growth_iterate
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (center : ℝ × ℝ) (baseRadius threshold : ℝ) (steps : Nat)
    (hthreshold : 1 ≤ threshold)
    (hdiameter : ∀ step, step ≤ steps →
      1 ≤ 2 * squareGrowthRadius baseRadius threshold step)
    (hBoundarySmall : ∀ step, step < steps →
      48 * squareGrowthRadius baseRadius threshold (step + 1) * threshold +
          ((∑ q ∈ squareQubits embedding center
              (squareGrowthRadius baseRadius threshold step),
            P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) < d)
    (hRecoveryBase :
      ∃ recovery : QuantumChannel
          (squareSubsystem embedding center baseRadius).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (squareSubsystem embedding center baseRadius).complementSystem
          P.semanticCode
          (squareSubsystem embedding center baseRadius).erasureChannelFromRegister recovery) :
    ∃ recovery : QuantumChannel
        (squareSubsystem embedding center
          (squareGrowthRadius baseRadius threshold steps)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (squareSubsystem embedding center
          (squareGrowthRadius baseRadius threshold steps)).complementSystem
        P.semanticCode
        (squareSubsystem embedding center
          (squareGrowthRadius baseRadius threshold steps)).erasureChannelFromRegister recovery := by sorry
