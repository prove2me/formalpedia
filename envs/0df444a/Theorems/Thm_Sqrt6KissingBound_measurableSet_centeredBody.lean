-- Prove2me | Theorems.Thm_Sqrt6KissingBound_measurableSet_centeredBody
-- name    : Sqrt6KissingBound.measurableSet_centeredBody
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T06:08:09.087502+00:00
-- url     : https://prove2.me/theorems/52faef62-a3a0-5294-9fdb-44c97a1d96eb
-- title:
--   Sqrt6 Kissing Bound: measurable Set centered Body
-- statement:
--   The Sqrt6 Kissing Bound construction uses the measurable Set centered Body property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBody.lean#L19-L23
-- source:
--   https://github.com/sebastienpalcoux/sqrt6-kissing-bound/blob/cc87870ad897f0fe15e3cdffd3d7acd15f0c1ba9/Sqrt6KissingBound/CenteredBody.lean#L19-L23

import Definitions.Def_Sqrt6KissingBound_CenteredBicone
import Definitions.Def_Sqrt6KissingBound_CenteredBody
set_option autoImplicit true
open Sqrt6KissingBound
noncomputable section
open Set Metric MeasureTheory

theorem Sqrt6KissingBound.measurableSet_centeredBody {k : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin (k + 2)))} (hS : MeasurableSet S)
    (x : EuclideanSpace ℝ (Fin (k + 2))) :
    MeasurableSet (centeredBody k S x) := by sorry
