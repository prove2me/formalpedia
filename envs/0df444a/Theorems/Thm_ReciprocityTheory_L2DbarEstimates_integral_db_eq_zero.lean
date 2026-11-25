-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integral_db_eq_zero
-- name    : ReciprocityTheory.L2DbarEstimates.integral_db_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:03:22.568223+00:00
-- url     : https://prove2.me/theorems/4fed9287-3c09-5ace-9248-fd3f01b2b6cf
-- title:
--   L2 Dbar Estimates: integral db eq zero
-- statement:
--   The L2 Dbar Estimates construction uses the integral db eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IntegralFderivApplyEqZero.lean#L194-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IntegralFderivApplyEqZero.lean#L194-L206

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_db

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section

theorem ReciprocityTheory.L2DbarEstimates.integral_db_eq_zero {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (j : Fin n) (g : M → ℂ) (hg : Ck n z 1 g) (hc : HasCompactSupport g) :
    ∫ x, db n z j g x ∂vol n z = 0 := by sorry
