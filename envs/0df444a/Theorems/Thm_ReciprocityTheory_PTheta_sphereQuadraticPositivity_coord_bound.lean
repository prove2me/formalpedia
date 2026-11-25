-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_coord_bound
-- name    : ReciprocityTheory.PTheta.sphereQuadraticPositivity.coord_bound
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:09:29.014671+00:00
-- url     : https://prove2.me/theorems/722d06f5-2406-4f5a-9a03-e1ee0511bb9f
-- title:
--   sphere Quadratic Positivity: coord bound
-- statement:
--   The sphere Quadratic Positivity construction uses the coord bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L186-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L186-L199

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

theorem ReciprocityTheory.PTheta.sphereQuadraticPositivity.coord_bound (β γ k a : ℝ) (hβ : 0 < β) (hγ : 0 ≤ γ) :
    -β * (k + a) ^ 2 + γ * |k + a| ≤ -(β / 4) * k ^ 2 + (γ ^ 2 / (2 * β) + β / 2 * a ^ 2) := by sorry
