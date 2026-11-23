-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_C_moll_integrable
-- name    : ReciprocityTheory.L2DbarEstimates.C.moll_integrable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:18:30.195556+00:00
-- url     : https://prove2.me/theorems/9c82098f-b51d-43a9-8d34-0b9069ed4f02
-- title:
--   C: moll integrable
-- statement:
--   The C construction uses the moll integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegIndep.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/WeakHolomorphy/RegIndep.lean#L9-L10

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_MeasurableEmbeddingRotAbout
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegConv
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_RegIndep
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

theorem ReciprocityTheory.L2DbarEstimates.C.moll_integrable (n : ℕ) {t : ℝ} (ht : 0 < t) : Integrable (moll n t) := by sorry
