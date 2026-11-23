-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_cdo_wd
-- name    : ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cdo_wd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:31:20.249984+00:00
-- url     : https://prove2.me/theorems/6fc09f53-21b2-476d-ba0a-b35bc39a14ad
-- title:
--   Monge Ampere Integrability: cdo wd
-- statement:
--   The Monge Ampere Integrability construction uses the cdo wd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/DetUpdateColEq.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/DetUpdateColEq.lean#L16-L24

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

theorem ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cdo_wd {Ω : Set (V n)} (hΩ : IsOpen Ω) {g : V n → ℂ} (hg : ContDiffOn ℝ ∞ g Ω)
    (j : Fin n) : ContDiffOn ℝ ∞ (wd n j g) Ω ∧ ContDiffOn ℝ ∞ (wdb n j g) Ω := by sorry
