-- Prove2me | Theorems.Thm_QEC_Locality_exists_gridBadPointSet_card_le
-- name    : QEC.Locality.exists_gridBadPointSet_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:44:17.454628+00:00
-- url     : https://prove2.me/theorems/8a5aab7b-0893-4d3a-ac23-524e1ea3fb26
-- title:
--   Locality: exists grid Bad Point Set card le
-- statement:
--   There is a translation whose candidate grid-bad point set has the explicit
--   #385 count.  This is only an averaging/counting result: it does not prove that
--   the set is a separator or that either complementary region is correctable.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1901-L1918
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/RecursivePartition.lean#L1901-L1918

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

theorem QEC.Locality.exists_gridBadPointSet_card_le
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold w ell : ℝ)
    (hell : 0 < ell) (hscale : 4 * ell ≤ w) :
    ∃ t : GridTranslation w,
      ((gridBadPointSet P embedding threshold w ell t).card : ℝ) ≤
        (32 * ell ^ 2 / w ^ 2) * Fintype.card ι +
          (32 * ell / w) * P.longInteractionCount embedding threshold := by sorry
