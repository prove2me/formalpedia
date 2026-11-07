-- Prove2me | Theorems.Thm_QEC_Locality_not_mem_daiLiKGeDSeparator_not_badRectangleVertex
-- name    : QEC.Locality.not_mem_daiLiKGeDSeparator_not_badRectangleVertex
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:22:01.182302+00:00
-- url     : https://prove2.me/theorems/fcf9e020-a123-425b-8773-72fc361b7859
-- title:
--   Locality: not mem dai Li KGe DSeparator not bad Rectangle Vertex
-- statement:
--   Avoiding the concrete `k >= d` separator excludes every vertex
--   neighborhood of every actual indexed bad rectangle.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3984-L3998
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L3984-L3998

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

theorem QEC.Locality.not_mem_daiLiKGeDSeparator_not_badRectangleVertex
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (q : ι) (hNotSeparator : q ∉ daiLiKGeDSeparator P embedding threshold w ell t cells rectangles)
    (cell : ℤ × ℤ) (hCell : cell ∈ cells) (slot : ℕ)
    (hSlot : slot < (rectangles cell).length) (vertex : Fin 4) :
    q ∉ daiLiVertexNeighborhoodQubits embedding ell
      (daiLiRectangleVertex ((rectangles cell).get ⟨slot, hSlot⟩) vertex) := by sorry
