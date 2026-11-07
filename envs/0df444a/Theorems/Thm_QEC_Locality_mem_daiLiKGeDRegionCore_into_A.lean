-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiKGeDRegionCore_into_A
-- name    : QEC.Locality.mem_daiLiKGeDRegionCore_into_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:11:08.551858+00:00
-- url     : https://prove2.me/theorems/5042134f-464b-426e-a8ef-b879776b565b
-- title:
--   Locality: mem dai Li KGe DRegion Core into A
-- statement:
--   One selected finite source-region core belongs to the assembled `A`
--   subsystem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3925-L3940
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3925-L3940

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

theorem QEC.Locality.mem_daiLiKGeDRegionCore_into_A
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (region : DaiLiKGeDRegionIndex)
    (hRegion : region ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles) (q : ι)
    (hq : q ∈ daiLiKGeDRegionCoreQubits P embedding threshold w ell t cells rectangles region) :
    q ∈ (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected := by sorry
