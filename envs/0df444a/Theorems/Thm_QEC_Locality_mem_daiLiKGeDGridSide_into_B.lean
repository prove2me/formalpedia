-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiKGeDGridSide_into_B
-- name    : QEC.Locality.mem_daiLiKGeDGridSide_into_B
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:09:42.311106+00:00
-- url     : https://prove2.me/theorems/0d923f25-9a02-48d5-a210-37d9b594673e
-- title:
--   Locality: mem dai Li KGe DGrid Side into B
-- statement:
--   One selected canonical grid side belongs to the assembled untrimmed `B`
--   subsystem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3944-L3959
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3944-L3959

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

theorem QEC.Locality.mem_daiLiKGeDGridSide_into_B
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (side : DaiLiGridSideIndex)
    (hSide : side ∈ daiLiGridSideCandidates embedding w (gridOrigin w t)) (q : ι)
    (hq : q ∈ daiLiKGeDGridSideQubits P embedding threshold w ell t cells rectangles side) :
    q ∈ (daiLiKGeDBSubsystem P embedding d threshold w ell t cells rectangles).selected := by sorry
