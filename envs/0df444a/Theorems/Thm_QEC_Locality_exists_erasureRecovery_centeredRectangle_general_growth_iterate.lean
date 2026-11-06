-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_centeredRectangle_general_growth_iterate
-- name    : QEC.Locality.exists_erasureRecovery_centeredRectangle_general_growth_iterate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:04:51.467779+00:00
-- url     : https://prove2.me/theorems/3b36dd25-c25e-46f9-80f8-28c7708ed876
-- title:
--   Locality: exists erasure Recovery centered Rectangle general growth iterate
-- statement:
--   Finite iteration of independently moving rectangle half-sides.  The
--   caller provides only geometric/numerical inequalities and a distance-small
--   base; every CPTP witness, including every intermediate boundary recovery, is
--   constructed internally.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1428-L1496
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1428-L1496

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

theorem QEC.Locality.exists_erasureRecovery_centeredRectangle_general_growth_iterate
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (center : ℝ × ℝ) (horizontalRadius verticalRadius : ℕ → ℝ)
    (threshold : ℝ) (steps : ℕ) (hThreshold : 1 ≤ threshold)
    (hHorizontalDiameter : ∀ step, step ≤ steps →
      1 ≤ 2 * horizontalRadius step)
    (hVerticalDiameter : ∀ step, step ≤ steps →
      1 ≤ 2 * verticalRadius step)
    (hHorizontalMonotone : ∀ step, step < steps →
      horizontalRadius step ≤ horizontalRadius (step + 1))
    (hVerticalMonotone : ∀ step, step < steps →
      verticalRadius step ≤ verticalRadius (step + 1))
    (hHorizontalInset : ∀ step, step < steps →
      horizontalRadius (step + 1) - threshold ≤ horizontalRadius step)
    (hVerticalInset : ∀ step, step < steps →
      verticalRadius (step + 1) - threshold ≤ verticalRadius step)
    (hBoundarySmall : ∀ step, step < steps →
      48 * (horizontalRadius (step + 1) + verticalRadius (step + 1) + threshold) *
          threshold +
        ((∑ q ∈ centeredRectangleQubits embedding center
          (horizontalRadius step) (verticalRadius step),
          P.daiLiInteractionCounter embedding threshold q : Nat) : ℝ) < d)
    (hBaseCard : (centeredRectangleQubits embedding center
      (horizontalRadius 0) (verticalRadius 0)).card < d) :
    ∃ recovery : QuantumChannel
        (centeredRectangleSubsystem embedding center
          (horizontalRadius steps) (verticalRadius steps)).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (centeredRectangleSubsystem embedding center
          (horizontalRadius steps) (verticalRadius steps)).complementSystem
        P.semanticCode
        (centeredRectangleSubsystem embedding center
          (horizontalRadius steps) (verticalRadius steps)).erasureChannelFromRegister
          recovery := by sorry
