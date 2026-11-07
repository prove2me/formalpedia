-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiDGeK_realization
-- name    : QEC.Locality.exists_daiLiDGeK_realization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:25:31.618602+00:00
-- url     : https://prove2.me/theorems/40376bcc-b71d-4b83-b11c-b194c3b9b49c
-- title:
--   Locality: exists dai Li DGe K realization
-- statement:
--   Executable Case-2 handoff for #387.  A single averaged translation produces
--   the exact B/B'/C routing, an empty bad-square family, a concrete CPTP
--   recovery for each of `A` and `B`, and the distinct-unordered interaction
--   separator bound.  The fourth-root scale and width are named above; a later
--   count-composition node discharges their remaining numerical substitution.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L1112-L1177
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L1112-L1177

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

theorem QEC.Locality.exists_daiLiDGeK_realization
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell : ℝ)
    (hGlobal : 10 * (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) < d)
    (hThreshold : 1 ≤ threshold) (hWidthNat : 1 ≤ w) (hEllNat : 1 ≤ ell)
    (hEll : 0 < ell) (hScale : 4 * ell ≤ w) (hThresholdEll : threshold ≤ ell)
    (hEdge : 1 ≤ 2 * ell) (hLongStrip : 1 ≤ w - 4 * ell)
    (hSmallStrip : 12 * ell * (w - 4 * ell) < d)
    (baseHorizontalRadius baseVerticalRadius : ℝ) (steps : ℕ)
    (hBaseHorizontal : baseHorizontalRadius ≤ w / 2)
    (hBaseVerticalGood : baseVerticalRadius ≤ w / 2)
    (hBaseVerticalBad : baseVerticalRadius ≤ 5 * ell / 2)
    (hBaseHorizontalDiameter : 1 ≤ 2 * baseHorizontalRadius)
    (hBaseVerticalDiameter : 1 ≤ 2 * baseVerticalRadius)
    (hReachHorizontal : w / 2 ≤ baseHorizontalRadius + steps * threshold)
    (hReachVerticalGood : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hReachVerticalBad : w / 2 ≤ baseVerticalRadius + steps * threshold)
    (hGoodBaseCard : ∀ (t : GridTranslation w) cell,
      cell ∈ embedding.gridOccupiedCells w (gridOrigin w t) →
        (centeredRectangleQubits embedding (daiLiGridCellCenter w (gridOrigin w t) cell)
          baseHorizontalRadius baseVerticalRadius).card < d)
    (hBoundaryBudget :
      48 * (w / 2 + w / 2 + threshold) * threshold + (d : ℝ) / 10 < d)
    (hShortPackingScale : 60 * w * ell < d) :
    ∃ t : GridTranslation w,
      ((daiLiDGeKSeparator P embedding threshold w ell t).card : ℝ) ≤
          (32 * ell ^ 2 / w ^ 2) * Fintype.card ι +
            64 * ell / w * (P.longInteractionCount embedding threshold : ℝ) ∧
      daiLiBadGridCells P embedding threshold d w (gridOrigin w t) = ∅ ∧
      (∃ recovery : QuantumChannel
          (daiLiDGeKASubsystem P embedding d threshold w ell t).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (daiLiDGeKASubsystem P embedding d threshold w ell t).complementSystem
          P.semanticCode
          (daiLiDGeKASubsystem P embedding d threshold w ell t).erasureChannelFromRegister
          recovery) ∧
      ∃ recovery : QuantumChannel
          (daiLiDGeKBSubsystem P embedding threshold w ell t).complementSystem
          (Qubit.QubitRegister ι),
        Correctable (Qubit.QubitRegister ι)
          (daiLiDGeKBSubsystem P embedding threshold w ell t).complementSystem
          P.semanticCode
          (daiLiDGeKBSubsystem P embedding threshold w ell t).erasureChannelFromRegister
          recovery := by sorry
