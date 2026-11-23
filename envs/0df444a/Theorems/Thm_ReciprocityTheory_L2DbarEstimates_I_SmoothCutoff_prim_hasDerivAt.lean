-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_SmoothCutoff_prim_hasDerivAt
-- name    : ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.prim_hasDerivAt
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:31:31.213632+00:00
-- url     : https://prove2.me/theorems/5ac549a2-7460-4387-88a6-735b48be185a
-- title:
--   Smooth Cutoff: prim has Deriv At
-- statement:
--   The Smooth Cutoff construction uses the prim has Deriv At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/Cutoff.lean#L45-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/Cutoff.lean#L45-L46

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

theorem ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.prim_hasDerivAt (t : ℝ) : HasDerivAt prim (bump t) t := by sorry
