-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_wd_zero_of_eqOn
-- name    : ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.wd_zero_of_eqOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:32:13.290157+00:00
-- url     : https://prove2.me/theorems/e042c596-10d3-4858-a083-4d83a4d3564d
-- title:
--   Monge Ampere Integrability: wd zero of eq On
-- statement:
--   The Monge Ampere Integrability construction uses the wd zero of eq On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/DetUpdateColEq.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/DetUpdateColEq.lean#L26-L32

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
open MeasureTheory Filter Topology Set
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.wd_zero_of_eqOn {Z : Set (V n)} (hZ : IsOpen Z) {g : V n → ℂ}
    (h : ∀ w ∈ Z, g w = 0) (j : Fin n) {y : V n} (hy : y ∈ Z) :
    wd n j g y = 0 ∧ wdb n j g y = 0 := by sorry
