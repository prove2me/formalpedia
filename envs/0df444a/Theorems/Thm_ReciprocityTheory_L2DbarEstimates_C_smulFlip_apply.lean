-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_smulFlip_apply
-- name    : ReciprocityTheory.L2DbarEstimates.C.smulFlip_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:15:39.773683+00:00
-- url     : https://prove2.me/theorems/c7eae0e3-bd2c-4a72-8e4c-d4a37f037040
-- title:
--   C: smul Flip apply
-- statement:
--   The C construction uses the smul Flip apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegConv.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegConv.lean#L11-L13

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_IntegralBumpProfOnePos
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem ReciprocityTheory.L2DbarEstimates.C.smulFlip_apply (a : ℂ) (r : ℝ) : smulFlip a r = (r : ℂ) * a := by sorry
