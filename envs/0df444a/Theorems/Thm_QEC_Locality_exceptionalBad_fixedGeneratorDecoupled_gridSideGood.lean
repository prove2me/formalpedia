-- Prove2me | Theorems.Thm_QEC_Locality_exceptionalBad_fixedGeneratorDecoupled_gridSideGood
-- name    : QEC.Locality.exceptionalBad_fixedGeneratorDecoupled_gridSideGood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:18:36.163464+00:00
-- url     : https://prove2.me/theorems/3b0d9d46-4379-43d9-bf09-2089158c8159
-- title:
--   Locality: exceptional Bad fixed Generator Decoupled grid Side Good
-- statement:
--   The exceptional `B_0` piece has no fixed-generator interaction with an actual
--   good edge strip.  Long interactions are excluded by the endpoint deletion;
--   short interactions are excluded by the proved `B_0 \u2212 B'` separation.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L494-L530
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/DistancePartition.lean#L494-L530

import Definitions.Def_QEC_Locality_OptimalTradeoff_CorrectablePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_DistancePartition
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
attribute [local instance] QEC.Locality.instClassicalDecidableDGeK

theorem QEC.Locality.exceptionalBad_fixedGeneratorDecoupled_gridSideGood
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) (hw : 0 < w) (hThresholdEll : threshold ≤ ell)
    (side : DaiLiGridSideIndex) :
    P.fixedGeneratorDecoupled
      ((daiLiDGeKExceptionalBadQubits P embedding threshold w ell t : Finset ι) : Set ι)
      ((daiLiGridSideGoodQubits P embedding threshold w ell (gridOrigin w t) side :
        Finset ι) : Set ι) := by sorry
