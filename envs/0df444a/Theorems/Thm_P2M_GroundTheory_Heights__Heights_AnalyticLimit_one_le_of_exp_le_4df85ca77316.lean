-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_AnalyticLimit_one_le_of_exp_le_4df85ca77316
-- name    : P2M_GroundTheory_Heights__Heights_AnalyticLimit_one_le_of_exp_le_4df85ca77316
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:28:32.978399+00:00
-- url     : https://prove2.me/theorems/2c8a8d7d-f48b-57ec-abf2-88f834ad5f4a
-- title:
--   P2 M Ground Theory Heights  Heights Analytic Limit one le of exp le 4df85ca77316: P2 M Ground Theory Heights  Heights Analytic Limit one le of exp le 4df85ca77316
-- statement:
--   The P2 M Ground Theory Heights  Heights Analytic Limit one le of exp le 4df85ca77316 construction uses the P2 M Ground Theory Heights  Heights Analytic Limit one le of exp le 4df85ca77316 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L31-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/AnalyticLimit/Telescoping.lean#L31-L33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_AnalyticLimit_Telescoping
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.AnalyticLimit
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData ell errE)
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_AnalyticLimit_one_le_of_exp_le_4df85ca77316 {y : ℝ} (h : Real.exp 1 ≤ y) : 1 ≤ y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«AnalyticLimit».«one_le_of_exp_le» := P2M_GroundTheory_Heights__Heights_AnalyticLimit_one_le_of_exp_le_4df85ca77316
