-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_regMax_bounds_7e37d99f8d7b
-- name    : P2M_GroundTheory_Heights__Heights_Regular_regMax_bounds_7e37d99f8d7b
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:18:35.739821+00:00
-- url     : https://prove2.me/theorems/7ac6d3f1-380c-4c67-82fe-1b07a892d0bd
-- title:
--   P2 M Ground Theory Heights  Heights Regular reg Max bounds 7e37d99f8d7b: P2 M Ground Theory Heights  Heights Regular reg Max bounds 7e37d99f8d7b
-- statement:
--   The P2 M Ground Theory Heights  Heights Regular reg Max bounds 7e37d99f8d7b construction uses the P2 M Ground Theory Heights  Heights Regular reg Max bounds 7e37d99f8d7b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsCompactImageClosureMid.lean#L29-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Regularisation/IsCompactImageClosureMid.lean#L29-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshRegMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsCompactImageClosureMid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open MeasureTheory Metric Filter Topology Set
open scoped ContDiff
open ReciprocityTheory.AnForm.A (IsPsh polyMax Mollifier molli shrink regMax tmax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open ReciprocityTheory.AnForm (levi)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Regular_regMax_bounds_7e37d99f8d7b {ι : Type} [Fintype ι] [Nonempty ι] {η : ℝ} (hη : 0 < η) (t : ι → ℝ) :
    tmax t ≤ regMax η t ∧ regMax η t ≤ tmax t + η / 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Regular».«regMax_bounds» := P2M_GroundTheory_Heights__Heights_Regular_regMax_bounds_7e37d99f8d7b
