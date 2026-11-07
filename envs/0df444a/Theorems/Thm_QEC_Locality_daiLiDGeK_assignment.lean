-- Prove2me | Theorems.Thm_QEC_Locality_daiLiDGeK_assignment
-- name    : QEC.Locality.daiLiDGeK_assignment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:19:00.458665+00:00
-- url     : https://prove2.me/theorems/9a364df0-3357-408c-ab4b-ab338805a08b
-- title:
--   Locality: dai Li DGe K assignment
-- statement:
--   Every physical qubit is assigned by the actual Case-2 geometry to the
--   sharper separator, `A`, or the complete recoverable `B`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L740-L776
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L740-L776

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

theorem QEC.Locality.daiLiDGeK_assignment
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w)
    (hGlobal : 10 * (∑ q : ι, P.daiLiInteractionCounter embedding threshold q) < d)
    (hw : 0 < w) (hEll : 0 < ell) (q : ι) :
    q ∈ daiLiDGeKSeparator P embedding threshold w ell t ∨
      q ∈ (daiLiDGeKASubsystem P embedding d threshold w ell t).selected ∨
        q ∈ (daiLiDGeKBSubsystem P embedding threshold w ell t).selected := by sorry
