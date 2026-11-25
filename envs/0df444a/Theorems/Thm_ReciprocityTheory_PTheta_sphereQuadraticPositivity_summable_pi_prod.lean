-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_summable_pi_prod
-- name    : ReciprocityTheory.PTheta.sphereQuadraticPositivity.summable_pi_prod
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:09:37.572335+00:00
-- url     : https://prove2.me/theorems/7d7bf422-0d0d-555c-aaf3-8b3a7fd40914
-- title:
--   sphere Quadratic Positivity: summable pi prod
-- statement:
--   The sphere Quadratic Positivity construction uses the summable pi prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L225-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L225-L235

import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_ThetaQuasiPeriodStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_NormInvSmulMemSphere
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open ReciprocityTheory ReciprocityTheory.PTheta ReciprocityTheory.PTheta.sphereQuadraticPositivity
variable {ι : Type*} [Fintype ι]

theorem ReciprocityTheory.PTheta.sphereQuadraticPositivity.summable_pi_prod {g : ι → ℤ → ℝ} (hg0 : ∀ i k, 0 ≤ g i k) (hg : ∀ i, Summable (g i)) :
    Summable (fun l : ι → ℤ => ∏ i, g i (l i)) := by sorry
