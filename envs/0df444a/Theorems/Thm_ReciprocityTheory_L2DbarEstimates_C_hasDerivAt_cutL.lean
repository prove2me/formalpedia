-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_hasDerivAt_cutL
-- name    : ReciprocityTheory.L2DbarEstimates.C.hasDerivAt_cutL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:14:38.231154+00:00
-- url     : https://prove2.me/theorems/73dd915b-b48b-4896-9cb5-dcdfef7443e8
-- title:
--   C: has Deriv At cut L
-- statement:
--   The C construction uses the has Deriv At cut L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtCutA.lean#L18-L21

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

theorem ReciprocityTheory.L2DbarEstimates.C.hasDerivAt_cutL {ε s : ℝ} (h : 0 < s + ε) : HasDerivAt (cutL ε) (s + ε)⁻¹ s := by sorry
