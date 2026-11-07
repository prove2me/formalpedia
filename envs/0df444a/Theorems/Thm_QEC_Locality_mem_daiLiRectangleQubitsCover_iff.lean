-- Prove2me | Theorems.Thm_QEC_Locality_mem_daiLiRectangleQubitsCover_iff
-- name    : QEC.Locality.mem_daiLiRectangleQubitsCover_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:13:07.567803+00:00
-- url     : https://prove2.me/theorems/de14e855-845d-4610-b312-94b5f0865300
-- title:
--   Locality: mem dai Li Rectangle Qubits Cover iff
-- statement:
--   Membership in the finite cover of actual rectangles has a concrete
--   rectangle-list witness.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L996-L1016
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L996-L1016

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

theorem QEC.Locality.mem_daiLiRectangleQubitsCover_iff
    (embedding : UnitSeparatedEmbedding2D ι)
    (rectangles : List ((ℝ × ℝ) × (ℝ × ℝ))) (q : ι) :
    q ∈ daiLiRectangleQubitsCover embedding rectangles ↔
      ∃ rectangle ∈ rectangles,
        q ∈ embedding.qubitsInRectangle rectangle.1 rectangle.2 := by sorry
