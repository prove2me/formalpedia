-- Prove2me | Theorems.Thm_QEC_Locality_exists_erasureRecovery_daiLiRectangleSideStrip_of_box_scale
-- name    : QEC.Locality.exists_erasureRecovery_daiLiRectangleSideStrip_of_box_scale
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:16:07.330366+00:00
-- url     : https://prove2.me/theorems/dc45f786-e68a-4986-a330-ee0f14b02fef
-- title:
--   Locality: exists erasure Recovery dai Li Rectangle Side Strip of box scale
-- statement:
--   Each box-scale subdivision side strip therefore obtains its CPTP erasure
--   recovery directly from the semantic distance API.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2229-L2252
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2229-L2252

import Definitions.Def_QEC_Locality_CorrectablePartition_SmallBoundary
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
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
attribute [local instance] QEC.Locality.instClassicalDecidableCorrectable

theorem QEC.Locality.exists_erasureRecovery_daiLiRectangleSideStrip_of_box_scale
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ)
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (ell w : ℝ) (lower upper : ℝ × ℝ) (hEll : 1 ≤ ell)
    (hCellWidth : 5 * ell ≤ w) (hSpan : upper.1 - lower.1 = w)
    (hMinimumHeight : 5 * ell ≤ upper.2 - lower.2)
    (hMaximumHeight : upper.2 - lower.2 ≤ w)
    (hSideScale : 12 * ell * w < d) (side : Fin 4) :
    ∃ recovery : QuantumChannel
        (daiLiRectangleSideStripSubsystem embedding ell lower upper side).complementSystem
        (Qubit.QubitRegister ι),
      Correctable (Qubit.QubitRegister ι)
        (daiLiRectangleSideStripSubsystem embedding ell lower upper side).complementSystem
        P.semanticCode
        (daiLiRectangleSideStripSubsystem embedding ell lower upper side).erasureChannelFromRegister
          recovery := by sorry
