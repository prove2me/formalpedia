-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_prim_le
-- name    : ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.prim_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:39.712929+00:00
-- url     : https://prove2.me/theorems/d124dc07-9cb5-460e-b6b0-3f0eb1c47aec
-- title:
--   Smooth Cutoff: prim le
-- statement:
--   The Smooth Cutoff construction uses the prim le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/Cutoff.lean#L98-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/Cutoff.lean#L98-L100

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

theorem ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.prim_le (t : ℝ) : prim t ≤ prim 1 := by sorry
