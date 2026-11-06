-- Prove2me | Theorems.Thm_QEC_Locality_card_gridBadPointSet_le_badCounts
-- name    : QEC.Locality.card_gridBadPointSet_le_badCounts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:05:06.356193+00:00
-- url     : https://prove2.me/theorems/eeadcae2-a322-4723-9681-46e4ea5c3a1a
-- title:
--   Locality: card grid Bad Point Set le bad Counts
-- statement:
--   The candidate grid-bad set is controlled by the two actual counts from #385.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1867-L1894
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1867-L1894

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

theorem QEC.Locality.card_gridBadPointSet_le_badCounts
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (t : GridTranslation w) :
    ((gridBadPointSet P embedding threshold w ell t).card : ℝ) ≤
      (vertexBadCount w (2 * ell) embedding.point t : ℝ) +
        (edgeBadCount w (2 * ell)
          (P.daiLiLongIncidencePoint embedding threshold) t : ℝ) := by sorry
