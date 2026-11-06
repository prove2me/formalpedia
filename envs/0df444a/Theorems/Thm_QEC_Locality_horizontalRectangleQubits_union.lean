-- Prove2me | Theorems.Thm_QEC_Locality_horizontalRectangleQubits_union
-- name    : QEC.Locality.horizontalRectangleQubits_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:05:16.690959+00:00
-- url     : https://prove2.me/theorems/c8084c7b-bc57-48dc-9080-5d5ee3668e6e
-- title:
--   Locality: horizontal Rectangle Qubits union
-- statement:
--   The Locality construction uses the horizontal Rectangle Qubits union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2078-L2089
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2078-L2089

import Definitions.Def_QEC_Locality_CorrectableRegions_CorrectableRegionClosure
import Definitions.Def_QEC_Locality_OptimalTradeoff_PackingTiling
import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
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
attribute [local instance] QEC.Locality.instClassicalDecidableRecursive

theorem QEC.Locality.horizontalRectangleQubits_union
    (embedding : UnitSeparatedEmbedding2D ι) (lower upper : ℝ × ℝ)
    (cut : ℝ) :
    lowerHorizontalRectangleQubits embedding lower upper cut ∪
        upperHorizontalRectangleQubits embedding lower upper cut =
      embedding.qubitsInRectangle lower upper := by sorry
