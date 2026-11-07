-- Prove2me | Theorems.Thm_QEC_Locality_exists_daiLiDGeK_source_case
-- name    : QEC.Locality.exists_daiLiDGeK_source_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:19:06.382728+00:00
-- url     : https://prove2.me/theorems/ccde3e05-5eff-4cce-b91e-65ff99102bc3
-- title:
--   Locality: exists dai Li DGe K source case
-- statement:
--   The source-scale Case-2 handoff uses one and the same selected translation for
--   the strict separator bound and for both CPTP recoveries.  It is the complete
--   internal `d >= k` B/B'/C result consumed by the subsequent dimension node.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L1184-L1271
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L1184-L1271

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

theorem QEC.Locality.exists_daiLiDGeK_source_case
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (threshold w ell k : ℝ)
    (hk : 0 < k) (hd : 0 < (d : ℝ)) (_hDGeK : k ≤ d)
    (hn : 0 < (Fintype.card ι : ℝ))
    (hDistanceDomain : (d : ℝ) ≤ Real.sqrt (k * Fintype.card ι))
    (hScale : ell = daiLiPrincipalFourthRootScale k d (Fintype.card ι))
    (hWidth : w = daiLiDGeKGridWidth d ell)
    (hLongCount : (P.longInteractionCount embedding threshold : ℝ) ≤ (d : ℝ) / 100)
    (hGridScale : 4 * ell ≤ w)
    (hThreshold : 1 ≤ threshold) (hWidthNat : 1 ≤ w) (hEllNat : 1 ≤ ell)
    (hThresholdEll : threshold ≤ ell)
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
      ((daiLiDGeKSeparator P embedding threshold w ell t).card : ℝ) < k ∧
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
