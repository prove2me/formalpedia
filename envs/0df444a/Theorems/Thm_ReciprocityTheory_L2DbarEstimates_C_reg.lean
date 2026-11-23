-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_reg
-- name    : ReciprocityTheory.L2DbarEstimates.C.reg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:39.083367+00:00
-- url     : https://prove2.me/theorems/3613e188-3d56-4f37-833e-4e9b0d3de4e8
-- title:
--   C: reg
-- statement:
--   The C construction uses the reg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegBall.lean#L36-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegBall.lean#L36-L76

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegIndep
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MollLeClosedBall
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegGlue
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegBall
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

theorem ReciprocityTheory.L2DbarEstimates.C.reg : RegStatement := by sorry
