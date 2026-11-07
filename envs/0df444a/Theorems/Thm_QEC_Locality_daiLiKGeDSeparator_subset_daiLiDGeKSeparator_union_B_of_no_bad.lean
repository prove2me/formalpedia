-- Prove2me | Theorems.Thm_QEC_Locality_daiLiKGeDSeparator_subset_daiLiDGeKSeparator_union_B_of_no_bad
-- name    : QEC.Locality.daiLiKGeDSeparator_subset_daiLiDGeKSeparator_union_B_of_no_bad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:18:45.667113+00:00
-- url     : https://prove2.me/theorems/e0c12fe7-c301-4a11-a025-01e066168761
-- title:
--   Locality: dai Li KGe DSeparator subset dai Li DGe KSeparator union B of no bad
-- statement:
--   In the no-bad-cell branch, every point of the older source separator is
--   either in the sharper Case-2 separator or is an exceptional long endpoint
--   which the Case-2 construction puts into `B`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L718-L736
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L718-L736

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

theorem QEC.Locality.daiLiKGeDSeparator_subset_daiLiDGeKSeparator_union_B_of_no_bad
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w)
    (hNoBad : daiLiBadGridCells P embedding threshold d w (gridOrigin w t) = ∅) :
    daiLiKGeDSeparator P embedding threshold w ell t
        (daiLiBadGridCells P embedding threshold d w (gridOrigin w t)) (fun _ => []) ⊆
      daiLiDGeKSeparator P embedding threshold w ell t ∪
        (daiLiDGeKBSubsystem P embedding threshold w ell t).selected := by sorry
