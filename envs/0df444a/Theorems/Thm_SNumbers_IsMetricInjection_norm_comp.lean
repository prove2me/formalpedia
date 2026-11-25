-- Prove2me | Theorems.Thm_SNumbers_IsMetricInjection_norm_comp
-- name    : SNumbers.IsMetricInjection.norm_comp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:09:11.128133+00:00
-- url     : https://prove2.me/theorems/a276e0f9-5eca-4071-afae-8c2f3729402a
-- title:
--   Is Metric Injection: norm comp
-- statement:
--   Post-composition with a metric injection preserves the operator norm:
--   `‖J ∘ T‖ = ‖T‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L104-L114
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L104-L114

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Injectivity
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.IsMetricInjection.norm_comp {J : Y →L[𝕜] Z} (hJ : IsMetricInjection J)
    (T : W →L[𝕜] Y) : ‖J.comp T‖ = ‖T‖ := by sorry
