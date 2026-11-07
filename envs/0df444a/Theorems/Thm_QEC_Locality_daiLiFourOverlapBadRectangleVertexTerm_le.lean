-- Prove2me | Theorems.Thm_QEC_Locality_daiLiFourOverlapBadRectangleVertexTerm_le
-- name    : QEC.Locality.daiLiFourOverlapBadRectangleVertexTerm_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:13:37.539208+00:00
-- url     : https://prove2.me/theorems/52632fff-5a21-48bd-842c-5b173158d629
-- title:
--   Locality: dai Li Four Overlap Bad Rectangle Vertex Term le
-- statement:
--   The finite fourfold closed-cell boundary charge preserves a quantitative
--   bad-rectangle vertex estimate.  `960` is a Lean-QEC conservative witness:
--   it comes from the proved factor-30 subdivision and the explicit overlap
--   factor four, not from a constant asserted in DL24.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1303-L1321
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/CorrectablePartition.lean#L1303-L1321

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

theorem QEC.Locality.daiLiFourOverlapBadRectangleVertexTerm_le
    (M badTotalF globalTotalF d k : Nat) (ell : ℝ)
    (hD : 0 < d) (hCount : M * d ≤ 30 * badTotalF)
    (hOverlap : badTotalF ≤ 4 * globalTotalF)
    (hGlobal : 50 * globalTotalF ≤ k) :
    384 * ell ^ 2 * (M : ℝ) ≤ 960 * ell ^ 2 * (k : ℝ) / (d : ℝ) := by sorry
