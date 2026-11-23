-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_hasDerivAt_cutP
-- name    : ReciprocityTheory.L2DbarEstimates.C.hasDerivAt_cutP
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:04.918622+00:00
-- url     : https://prove2.me/theorems/e2abe8bf-222b-4816-853e-48107ea3c27c
-- title:
--   C: has Deriv At cut P
-- statement:
--   The C construction uses the has Deriv At cut P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L23-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L23-L29

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA
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
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.C.hasDerivAt_cutP {ε s : ℝ} (h : 0 < s + ε) : HasDerivAt (cutP ε) (halfLogRatioSqDeriv ε s) s := by sorry
