-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_cdo_adj
-- name    : ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cdo_adj
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T10:56:44.344497+00:00
-- url     : https://prove2.me/theorems/0300ec2f-efb9-4af4-95cc-c985353739eb
-- title:
--   Monge Ampere Integrability: cdo adj
-- statement:
--   The Monge Ampere Integrability construction uses the cdo adj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/DetUpdateColEq.lean#L85-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/DetUpdateColEq.lean#L85-L95

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

theorem ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cdo_adj {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {S : Set X} {m : WithTop ℕ∞}
    (F : Fin n → Fin n → X → ℂ) (hF : ∀ i j, ContDiffOn ℝ m (F i j) S) (k l : Fin n) :
    ContDiffOn ℝ m (fun w => (Matrix.of fun i j => F i j w).adjugate k l) S := by sorry
