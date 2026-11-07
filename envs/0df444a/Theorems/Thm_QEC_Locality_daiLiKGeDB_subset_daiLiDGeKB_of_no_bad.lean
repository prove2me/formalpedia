-- Prove2me | Theorems.Thm_QEC_Locality_daiLiKGeDB_subset_daiLiDGeKB_of_no_bad
-- name    : QEC.Locality.daiLiKGeDB_subset_daiLiDGeKB_of_no_bad
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:18:40.727115+00:00
-- url     : https://prove2.me/theorems/25a095ef-b8a3-49b9-a3fc-952bb77e21e0
-- title:
--   Locality: dai Li KGe DB subset dai Li DGe KB of no bad
-- statement:
--   With no bad cells, the older complete cell-assignment `B` is contained in
--   the Case-2 `B`: its grid-side points avoid every long endpoint, while its
--   internal bad-rectangle family is empty.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L683-L713
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L683-L713

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

theorem QEC.Locality.daiLiKGeDB_subset_daiLiDGeKB_of_no_bad
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w)
    (hNoBad : daiLiBadGridCells P embedding threshold d w (gridOrigin w t) = ∅) :
    (daiLiKGeDBSubsystem P embedding d threshold w ell t
      (daiLiBadGridCells P embedding threshold d w (gridOrigin w t))
      (fun _ => [])).selected ⊆
      (daiLiDGeKBSubsystem P embedding threshold w ell t).selected := by sorry
