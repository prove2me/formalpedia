-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_norm_inv_smul_mem_sphere
-- name    : ReciprocityTheory.PTheta.sphereQuadraticPositivity.norm_inv_smul_mem_sphere
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:20.827343+00:00
-- url     : https://prove2.me/theorems/ad0b8ad1-65b1-4bc5-a34b-e80313da13a1
-- title:
--   sphere Quadratic Positivity: norm inv smul mem sphere
-- statement:
--   The sphere Quadratic Positivity construction uses the norm inv smul mem sphere property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L21-L24

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

theorem ReciprocityTheory.PTheta.sphereQuadraticPositivity.norm_inv_smul_mem_sphere {x : ι → ℝ} (hx : x ≠ 0) :
    ‖x‖⁻¹ • x ∈ Metric.sphere (0 : ι → ℝ) 1 := by sorry
