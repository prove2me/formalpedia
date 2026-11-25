-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_quad_pos_of_sphere
-- name    : ReciprocityTheory.PTheta.sphereQuadraticPositivity.quad_pos_of_sphere
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:09:26.507651+00:00
-- url     : https://prove2.me/theorems/11e020db-f33d-53c8-bb93-4bc422677dca
-- title:
--   sphere Quadratic Positivity: quad pos of sphere
-- statement:
--   The sphere Quadratic Positivity construction uses the quad pos of sphere property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L26-L32

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

theorem ReciprocityTheory.PTheta.sphereQuadraticPositivity.quad_pos_of_sphere (A : Matrix ι ι ℝ)
    (h : ∀ y ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < y ⬝ᵥ (A *ᵥ y)) (x : ι → ℝ) (hx : x ≠ 0) :
    0 < x ⬝ᵥ (A *ᵥ x) := by sorry
