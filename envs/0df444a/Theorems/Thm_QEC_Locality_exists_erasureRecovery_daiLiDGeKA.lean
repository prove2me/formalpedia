-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiDGeKA
-- name    : QEC.Locality.exists_erasureRecovery_daiLiDGeKA
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:14:18.687268+00:00
-- url     : https://prove2.me/theorems/78c0aafe-9372-4818-97e6-2fabb29bac1d
-- title:
--   Locality: exists erasure Recovery dai Li DGe KA
-- statement:
--   The internal Case-2 `A` family has a concrete CPTP recovery.  The only
--   quantitative hypotheses are the finite clipped-growth/packing checks needed
--   by the already proved cell recovery; no `A` region, rectangle list, or
--   recovery channel is accepted as an input.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L837-L897
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L837-L897

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

theorem QEC.Locality.exists_erasureRecovery_daiLiDGeKA
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ) (t : GridTranslation w)
    (hGlobal : 10 * (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) < d)
    (hThreshold : 1 ≤ threshold) (hWidthNat : 1 ≤ w) (hEllNat : 1 ≤ ell)
    (hEll : 0 < ell) (hWidth : 0 < w) (hThresholdEll : threshold ≤ ell)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVerticalGood : baseVerticalRadius ≤ w / 2)
    (hBaseVerticalBad : baseVerticalRadius ≤ 5 * ell / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * threshold)
    (hReachVerticalGood : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hReachVerticalBad : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hGoodBaseCard : ∀ cell, cell ∈ embedding.gridOccupiedCells w (gridOrigin w t) →
      (centeredRectangleQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell)
        baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + threshold) * threshold + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d) :
    ∃ recovery : QuantumChannel
        (daiLiDGeKASubsystem P embedding d threshold w ell t).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiDGeKASubsystem P embedding d threshold w ell t).complementSystem
        P.semanticCode
        (daiLiDGeKASubsystem P embedding d threshold w ell t).erasureChannelFromRegister
        recovery := by sorry
