-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_sum_sq_le
-- name    : ReciprocityTheory.PTheta.sphereQuadraticPositivity.sum_sq_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:09:32.013615+00:00
-- url     : https://prove2.me/theorems/8feebf4f-6bf9-5e18-a768-407e9bcca22f
-- title:
--   sphere Quadratic Positivity: sum sq le
-- statement:
--   The sphere Quadratic Positivity construction uses the sum sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L34-L40

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

theorem ReciprocityTheory.PTheta.sphereQuadraticPositivity.sum_sq_le (x : ι → ℝ) : ∑ i, x i ^ 2 ≤ (Fintype.card ι) * ‖x‖ ^ 2 := by sorry
