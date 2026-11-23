-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_ap_holo_jac
-- name    : ReciprocityTheory.L2DbarEstimates.I.ap_holo_jac
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:30:42.007635+00:00
-- url     : https://prove2.me/theorems/1d7ee3b2-fc07-4c4d-bf51-8184f21ed816
-- title:
--   I: ap holo jac
-- statement:
--   The I construction uses the ap holo jac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyA.lean#L48-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/ApplyA.lean#L48-L63

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_ApplyA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

theorem ReciprocityTheory.L2DbarEstimates.I.ap_holo_jac {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (g : Fin n → M → ℂ)
    (hg : ∀ i, Holo n z (g i)) : Holo n z (jac n z g) := by sorry
