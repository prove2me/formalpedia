-- Prove2me | Theorems.Thm_QEC_Locality_daiLiRectangleQubits_eq_centeredRectangleQubits
-- name    : QEC.Locality.daiLiRectangleQubits_eq_centeredRectangleQubits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:10:26.866857+00:00
-- url     : https://prove2.me/theorems/0d018ec9-c086-4eb8-8317-c16b3cd7c62b
-- title:
--   Locality: dai Li Rectangle Qubits eq centered Rectangle Qubits
-- statement:
--   The rectangle representation used by #496 agrees exactly with the
--   center-and-half-side representation used by actual growth.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2005-L2027
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L2005-L2027

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

theorem QEC.Locality.daiLiRectangleQubits_eq_centeredRectangleQubits
    (embedding : UnitSeparatedEmbedding2D ι) (lower upper : ℝ × ℝ) :
    embedding.qubitsInRectangle lower upper =
      centeredRectangleQubits embedding (daiLiRectangleCenter lower upper)
        (daiLiRectangleHorizontalRadius lower upper)
        (daiLiRectangleVerticalRadius lower upper) := by sorry
