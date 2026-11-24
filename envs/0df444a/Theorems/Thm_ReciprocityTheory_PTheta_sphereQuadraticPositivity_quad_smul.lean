-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_quad_smul
-- name    : ReciprocityTheory.PTheta.sphereQuadraticPositivity.quad_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:05.211801+00:00
-- url     : https://prove2.me/theorems/96bca240-89f4-43c9-843a-e55bdc99cf36
-- title:
--   sphere Quadratic Positivity: quad smul
-- statement:
--   The sphere Quadratic Positivity construction uses the quad smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L11-L14

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

theorem ReciprocityTheory.PTheta.sphereQuadraticPositivity.quad_smul (A : Matrix ι ι ℝ) (r : ℝ) (x : ι → ℝ) :
    (r • x) ⬝ᵥ (A *ᵥ (r • x)) = r ^ 2 * (x ⬝ᵥ (A *ᵥ x)) := by sorry
