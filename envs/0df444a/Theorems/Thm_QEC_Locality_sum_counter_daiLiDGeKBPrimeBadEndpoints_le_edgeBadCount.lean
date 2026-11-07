-- Prove2me | Theorems.Thm_QEC_Locality_sum_counter_daiLiDGeKBPrimeBadEndpoints_le_edgeBadCount
-- name    : QEC.Locality.sum_counter_daiLiDGeKBPrimeBadEndpoints_le_edgeBadCount
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:18:13.970055+00:00
-- url     : https://prove2.me/theorems/6b791b4c-677e-46ef-b921-c4edf8ba9884
-- title:
--   Locality: sum counter dai Li DGe KBPrime Bad Endpoints le edge Bad Count
-- statement:
--   Every selected B'-endpoint contributes all of its incident long-edge slots to
--   the edge-bad incidence set.  This is the finite bridge that prevents replacing
--   distinct unordered interactions by an untracked ordered-pair count.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L222-L259
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L222-L259

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

theorem QEC.Locality.sum_counter_daiLiDGeKBPrimeBadEndpoints_le_edgeBadCount
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) :
    (∑ q ∈ daiLiDGeKBPrimeBadEndpoints P embedding threshold w ell t,
      P.daiLiInteractionCounter embedding threshold q) ≤
      edgeBadCount w (2 * ell)
        (P.daiLiLongIncidencePoint embedding threshold) t := by sorry
