-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_isCutoff_chi
-- name    : ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.isCutoff_chi
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:33.281773+00:00
-- url     : https://prove2.me/theorems/791e797d-bb77-4689-a78c-8b8a6f73c7c7
-- title:
--   Smooth Cutoff: is Cutoff chi
-- statement:
--   The Smooth Cutoff construction uses the is Cutoff chi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/Cutoff.lean#L107-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/Cutoff.lean#L107-L121

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

theorem ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.isCutoff_chi : IsCutoff chi := by sorry
