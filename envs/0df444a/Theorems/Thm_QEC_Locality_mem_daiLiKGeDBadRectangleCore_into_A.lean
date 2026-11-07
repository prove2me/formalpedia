-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiKGeDBadRectangleCore_into_A
-- name    : QEC.Locality.mem_daiLiKGeDBadRectangleCore_into_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:17:19.418377+00:00
-- url     : https://prove2.me/theorems/955e64d1-8920-495f-bdb9-e64f513753ce
-- title:
--   Locality: mem dai Li KGe DBad Rectangle Core into A
-- statement:
--   A strict, separator-free point of one indexed actual bad rectangle is
--   assigned to the concrete `A` subsystem.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L4002-L4029
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L4002-L4029

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

theorem QEC.Locality.mem_daiLiKGeDBadRectangleCore_into_A
    (P : StabilizerCode.BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : ℕ) (threshold w ell : ℝ)
    (t : GridTranslation w) (cells : Finset (ℤ × ℤ))
    (rectangles : (ℤ × ℤ) → List ((ℝ × ℝ) × (ℝ × ℝ)))
    (cell : ℤ × ℤ) (slot : ℕ) (hSlot : slot < (rectangles cell).length)
    (hCandidate : Sum.inr (cell, slot) ∈ daiLiKGeDRegionCandidates P embedding threshold d
      w (gridOrigin w t) rectangles) (q : ι)
    (hRect : q ∈ embedding.qubitsInRectangle
      ((rectangles cell).get ⟨slot, hSlot⟩).1 ((rectangles cell).get ⟨slot, hSlot⟩).2)
    (hNotSeparator : q ∉ daiLiKGeDSeparator P embedding threshold w ell t cells rectangles)
    (hStrict : ((rectangles cell).get ⟨slot, hSlot⟩).1.1 + ell < (embedding.point q).1 ∧
      (embedding.point q).1 < ((rectangles cell).get ⟨slot, hSlot⟩).2.1 - ell ∧
        ((rectangles cell).get ⟨slot, hSlot⟩).1.2 + ell < (embedding.point q).2 ∧
          (embedding.point q).2 < ((rectangles cell).get ⟨slot, hSlot⟩).2.2 - ell) :
    q ∈ (daiLiKGeDASubsystem P embedding d threshold w ell t cells rectangles).selected := by sorry
