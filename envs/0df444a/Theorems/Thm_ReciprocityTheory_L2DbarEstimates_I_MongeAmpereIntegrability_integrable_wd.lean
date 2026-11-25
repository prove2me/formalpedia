-- Prove2me | Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_MongeAmpereIntegrability_integrable_wd
-- name    : ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.integrable_wd
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:04:24.177228+00:00
-- url     : https://prove2.me/theorems/f96a03c0-ea46-4ef4-a751-80f3a29113fe
-- title:
--   Monge Ampere Integrability: integrable wd
-- statement:
--   The Monge Ampere Integrability construction uses the integrable wd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/IntegrableWd.lean#L16-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/L2DbarEstimates/LeviForms/IntegrableWd.lean#L16-L25

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_IntegrableWd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Set
open scoped ENNReal ContDiff
noncomputable section
open ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability
variable {n : ℕ}

theorem ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.integrable_wd {H : V n → ℂ} (hH : ContDiff ℝ 1 H) (hc : HasCompactSupport H)
    (j : Fin n) : Integrable (wd n j H) := by sorry
