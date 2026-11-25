-- Prove2me | Theorems.Thm_ReciprocityTheory_PTheta_sphereQuadraticPositivity_quad_lower
-- name    : ReciprocityTheory.PTheta.sphereQuadraticPositivity.quad_lower
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:09:20.849719+00:00
-- url     : https://prove2.me/theorems/d552f676-88f5-5547-99e1-9fc4d7d7c41c
-- title:
--   sphere Quadratic Positivity: quad lower
-- statement:
--   The sphere Quadratic Positivity construction uses the quad lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L42-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ThetaQuasiPeriods/NormInvSmulMemSphere.lean#L42-L91

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

theorem ReciprocityTheory.PTheta.sphereQuadraticPositivity.quad_lower {X : Type*} [TopologicalSpace X] (Mf : X → Matrix ι ι ℝ) (hc : Continuous Mf)
    (K : Set X) (hK : IsCompact K) (hpos : ∀ p ∈ K, (Mf p).PosDef) :
    ∃ c > 0, ∀ p ∈ K, ∀ x : ι → ℝ, c * ∑ i, x i ^ 2 ≤ x ⬝ᵥ (Mf p *ᵥ x) := by sorry
