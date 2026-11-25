-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_symPart_posDef_of_sphere
-- name    : ReciprocityTheory.PTheta.sphereQuadraticPositivity.symPart_posDef_of_sphere
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:09:42.977116+00:00
-- url     : https://prove2.me/theorems/cd62ecc3-0973-55ac-8548-150cd4f47256
-- title:
--   sphere Quadratic Positivity: sym Part pos Def of sphere
-- statement:
--   The sphere Quadratic Positivity construction uses the sym Part pos Def of sphere property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L97-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L97-L100

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

theorem ReciprocityTheory.PTheta.sphereQuadraticPositivity.symPart_posDef_of_sphere (A : Matrix ι ι ℝ)
    (h : ∀ y ∈ Metric.sphere (0 : ι → ℝ) 1, 0 < y ⬝ᵥ ((A + Aᵀ) *ᵥ y)) : (A + Aᵀ).PosDef := by sorry
