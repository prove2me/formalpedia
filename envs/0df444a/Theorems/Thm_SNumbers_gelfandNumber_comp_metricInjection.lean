-- Prove2me | Theorems.Thm_SNumbers_gelfandNumber_comp_metricInjection
-- name    : SNumbers.gelfandNumber_comp_metricInjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T01:31:34.894889+00:00
-- url     : https://prove2.me/theorems/27310c53-abd2-4b24-a10d-0726969bcb7b
-- title:
--   SNumbers: gelfand Number comp metric Injection
-- statement:
--   `cₙ(J ∘ S) = cₙ(S)` for every metric injection `J`: the infimum sets
--   defining the two Gelfand numbers coincide term by term.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L208-L219
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L208-L219

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

theorem SNumbers.gelfandNumber_comp_metricInjection {J : Y →L[𝕜] Z}
    (hJ : IsMetricInjection J) (S : X →L[𝕜] Y) (n : ℕ) :
    gelfandNumber (J.comp S) n = gelfandNumber S n := by sorry
