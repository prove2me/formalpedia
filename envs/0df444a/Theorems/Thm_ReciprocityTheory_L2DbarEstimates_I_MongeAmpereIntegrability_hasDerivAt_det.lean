-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_hasDerivAt_det
-- name    : ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.hasDerivAt_det
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:57:44.836064+00:00
-- url     : https://prove2.me/theorems/b20ab28a-b313-50f2-b7e2-c912baed9a97
-- title:
--   Monge Ampere Integrability: has Deriv At det
-- statement:
--   The Monge Ampere Integrability construction uses the has Deriv At det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/DetUpdateColEq.lean#L124-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/DetUpdateColEq.lean#L124-L152

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

theorem ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.hasDerivAt_det (A B : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (A + (s : ℂ) • B).det)
      (∑ k, ∑ j, (A + (t : ℂ) • B).adjugate k j * B j k) t := by sorry
