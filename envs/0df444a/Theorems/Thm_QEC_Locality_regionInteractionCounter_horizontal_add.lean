-- Prove2me | Theorems.Thm_QEC_Locality_regionInteractionCounter_horizontal_add
-- name    : QEC.Locality.regionInteractionCounter_horizontal_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:46:15.796297+00:00
-- url     : https://prove2.me/theorems/e4bbda4d-f216-483d-ba8f-c63c3f550a88
-- title:
--   Locality: region Interaction Counter horizontal add
-- statement:
--   Endpoint incidences add exactly across one genuine horizontal subdivision.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2092-L2106
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L2092-L2106

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

theorem QEC.Locality.regionInteractionCounter_horizontal_add
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold : ℝ)
    (lower upper : ℝ × ℝ) (cut : ℝ) :
    regionInteractionCounter P embedding threshold
        (lowerHorizontalRectangleQubits embedding lower upper cut) +
      regionInteractionCounter P embedding threshold
        (upperHorizontalRectangleQubits embedding lower upper cut) =
      regionInteractionCounter P embedding threshold
        (embedding.qubitsInRectangle lower upper) := by sorry
