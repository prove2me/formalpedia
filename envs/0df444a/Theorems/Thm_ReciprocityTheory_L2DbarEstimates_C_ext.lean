-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_ext
-- name    : ReciprocityTheory.L2DbarEstimates.C.ext
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:29:14.518633+00:00
-- url     : https://prove2.me/theorems/d6ddddca-6a70-43ac-b1e0-b4865ada9561
-- title:
--   C: ext
-- statement:
--   The C construction uses the ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtNull.lean#L9-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/ExtNull.lean#L9-L22

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtWeak
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegBall
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtNull
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

theorem ReciprocityTheory.L2DbarEstimates.C.ext : ExtStatement := by sorry
