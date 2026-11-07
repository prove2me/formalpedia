-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiKGeDInternalSideCandidates_iff
-- name    : QEC.Locality.mem_daiLiKGeDInternalSideCandidates_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:09:44.250598+00:00
-- url     : https://prove2.me/theorems/136a875a-e312-478f-afb7-04f5403b8c04
-- title:
--   Locality: mem dai Li KGe DInternal Side Candidates iff
-- statement:
--   Candidate membership says exactly that the cut belongs to a bad cell and
--   has a following rectangle; it is not an arbitrary list coordinate.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2989-L3017
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2989-L3017

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

theorem QEC.Locality.mem_daiLiKGeDInternalSideCandidates_iff
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ) (d : ℕ)
    (w : ℝ) (origin : ℝ × ℝ)
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (slot : ℕ) :
    (cell, slot) ∈ daiLiKGeDInternalSideCandidates P embedding threshold d w origin rectangles ↔
      cell ∈ daiLiBadGridCells P embedding threshold d w origin ∧
        slot + 1 < (rectangles cell).length := by sorry
