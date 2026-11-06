-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_centeredRectangle_of_good_clipped_growth
-- name    : QEC.Locality.exists_erasureRecovery_centeredRectangle_of_good_clipped_growth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:41:28.732881+00:00
-- url     : https://prove2.me/theorems/ac10676a-3b01-4696-bb27-a98e1393dfdc
-- title:
--   Locality: exists erasure Recovery centered Rectangle of good clipped growth
-- statement:
--   A good rectangle with bounded sides has a concrete CPTP recovery from a
--   finite clipped growth schedule.  This is the executable replacement for the
--   source's informal reduction of rectangles to squares: no enlargement imports
--   uncontrolled long incidences, and no recovery is accepted as a premise.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1521-L1697
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1521-L1697

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

theorem QEC.Locality.exists_erasureRecovery_centeredRectangle_of_good_clipped_growth
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (center : ℝ × ℝ)
    (baseHorizontalRadius baseVerticalRadius outerHorizontalRadius
      outerVerticalRadius threshold : ℝ) (steps : ℕ)
    (hThreshold : 1 ≤ threshold)
    (hBaseHorizontal : baseHorizontalRadius ≤ outerHorizontalRadius)
    (hBaseVertical : baseVerticalRadius ≤ outerVerticalRadius)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : outerHorizontalRadius ≤
      baseHorizontalRadius + steps * threshold)
    (hReachVertical : outerVerticalRadius ≤
      baseVerticalRadius + steps * threshold)
    (hBaseCard : (centeredRectangleQubits embedding center
      baseHorizontalRadius baseVerticalRadius).card < d)
    (hGoodCounter : 10 * regionInteractionCounter P embedding threshold
      (centeredRectangleQubits embedding center outerHorizontalRadius
        outerVerticalRadius) ≤ d)
    (hBoundaryBudget :
      48 * (outerHorizontalRadius + outerVerticalRadius + threshold) * threshold +
        (d : ℝ) / 10 < d) :
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
