-- Prove2me | Theorems.Thm_QEC_Locality_daiLiDGeK_partition_pairwise
-- name    : QEC.Locality.daiLiDGeK_partition_pairwise
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:14:22.075666+00:00
-- url     : https://prove2.me/theorems/3725b3a6-f6dd-4b96-9ebf-984332cdaad3
-- title:
--   Locality: dai Li DGe K partition pairwise
-- statement:
--   The Case-2 `A`, trimmed `B`, and residual regions are pairwise disjoint.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L154-L174
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L154-L174

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

theorem QEC.Locality.daiLiDGeK_partition_pairwise
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) :
    Disjoint (daiLiDGeKASubsystem P embedding d threshold w ell t).selected
      (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).selected ∧
    Disjoint (daiLiDGeKASubsystem P embedding d threshold w ell t).selected
      (daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected ∧
    Disjoint (daiLiDGeKTrimmedBSubsystem P embedding d threshold w ell t).selected
      (daiLiDGeKResidualSubsystem P embedding d threshold w ell t).selected := by sorry
