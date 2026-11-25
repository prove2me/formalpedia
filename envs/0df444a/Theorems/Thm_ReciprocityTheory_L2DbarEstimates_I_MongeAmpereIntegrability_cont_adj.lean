-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_cont_adj
-- name    : ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cont_adj
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:57:06.845784+00:00
-- url     : https://prove2.me/theorems/078bcd39-3719-4083-8c25-4112e4282962
-- title:
--   Monge Ampere Integrability: cont adj
-- statement:
--   The Monge Ampere Integrability construction uses the cont adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/DetUpdateColEq.lean#L97-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/DetUpdateColEq.lean#L97-L107

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

theorem ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cont_adj {X : Type*} [TopologicalSpace X] {S : Set X}
    (F : Fin n → Fin n → X → ℂ) (hF : ∀ i j, ContinuousOn (F i j) S) (k l : Fin n) :
    ContinuousOn (fun w => (Matrix.of fun i j => F i j w).adjugate k l) S := by sorry
