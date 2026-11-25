-- Prove2me | Theorems.Thm_SNumbers_deviationFromRestriction_comp_metricInjection
-- name    : SNumbers.deviationFromRestriction_comp_metricInjection
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T02:09:28.406798+00:00
-- url     : https://prove2.me/theorems/a234a7d0-08f9-43c8-82d4-ae881d982023
-- title:
--   SNumbers: deviation From Restriction comp metric Injection
-- statement:
--   The restriction-norm defining `cₙ` is preserved by post-composition
--   with a metric injection: `‖(J ∘ S)|_M‖ = ‖S|_M‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L199-L204
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L199-L204

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

theorem SNumbers.deviationFromRestriction_comp_metricInjection {J : Y →L[𝕜] Z}
    (hJ : IsMetricInjection J) (S : X →L[𝕜] Y) (M : Submodule 𝕜 X) :
    deviationFromRestriction (J.comp S) M = deviationFromRestriction S M := by sorry
