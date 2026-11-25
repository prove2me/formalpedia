-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_prim_of_one_le
-- name    : ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.prim_of_one_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:16.66377+00:00
-- url     : https://prove2.me/theorems/b4ea428b-3acb-4774-bb6d-59c8aa5cf7eb
-- title:
--   Smooth Cutoff: prim of one le
-- statement:
--   The Smooth Cutoff construction uses the prim of one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/Cutoff.lean#L66-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/Cutoff.lean#L66-L74

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

theorem ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.prim_of_one_le {t : ℝ} (ht : 1 ≤ t) : prim t = prim 1 := by sorry
