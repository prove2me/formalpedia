-- Prove2me | Theorems.Thm_SNumbers_IsMetricInjection_norm_le_one
-- name    : SNumbers.IsMetricInjection.norm_le_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:52:49.130967+00:00
-- url     : https://prove2.me/theorems/73eba29e-ef9e-4438-8714-43e14dfa7f53
-- title:
--   Is Metric Injection: norm le one
-- statement:
--   A metric injection is a contraction: `‖J‖ ≤ 1`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L98-L100
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L98-L100

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

theorem SNumbers.IsMetricInjection.norm_le_one {J : Y →L[𝕜] Z} (hJ : IsMetricInjection J) :
    ‖J‖ ≤ 1 := by sorry
