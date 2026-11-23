-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_integral_db_mul
-- name    : ReciprocityTheory.L2DbarEstimates.integral_db_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:29:32.197809+00:00
-- url     : https://prove2.me/theorems/9df24b60-8cb3-4aba-b151-00a1e94c52f8
-- title:
--   L2 Dbar Estimates: integral db mul
-- statement:
--   The L2 Dbar Estimates construction uses the integral db mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IntegralFderivApplyEqZero.lean#L236-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/ChartDerivatives/IntegralFderivApplyEqZero.lean#L236-L253

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

theorem ReciprocityTheory.L2DbarEstimates.integral_db_mul {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (z : M → V n) (hz : IsLocalHomeomorph z) (j : Fin n) (f g : M → ℂ) (hf : Ck n z 1 f) (hg : Ck n z 1 g) (hc : HasCompactSupport g) :
    ∫ x, db n z j f x * g x ∂vol n z = -∫ x, f x * db n z j g x ∂vol n z := by sorry
