-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiDGeKGoodSide_into_B
-- name    : QEC.Locality.mem_daiLiDGeKGoodSide_into_B
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:18:46.524125+00:00
-- url     : https://prove2.me/theorems/e03fa227-1cfe-49c6-b3d5-0be375d9adbf
-- title:
--   Locality: mem dai Li DGe KGood Side into B
-- statement:
--   Every selected good side component is contained in the concrete Case-2
--   `B` subsystem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L668-L678
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L668-L678

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

theorem QEC.Locality.mem_daiLiDGeKGoodSide_into_B
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (side : DaiLiGridSideIndex)
    (hSide : side ∈ daiLiDGeKGoodBIndices embedding w t) (q : ι)
    (hq : q ∈ daiLiGridSideGoodQubits P embedding threshold w ell (gridOrigin w t) side) :
    q ∈ (daiLiDGeKBSubsystem P embedding threshold w ell t).selected := by sorry
