-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_prim_one_ge
-- name    : ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.prim_one_ge
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:42.449732+00:00
-- url     : https://prove2.me/theorems/f27f1b27-13f2-4339-ad1b-3bf93a8376b6
-- title:
--   Smooth Cutoff: prim one ge
-- statement:
--   The Smooth Cutoff construction uses the prim one ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/Cutoff.lean#L76-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/Cutoff.lean#L76-L92

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_Cutoff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
open ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff

theorem ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.prim_one_ge : 2 / 5 ≤ prim 1 := by sorry
