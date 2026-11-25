-- Prove2me | Theorems.Thm_SNumbers_IsMetricSurjection_norm_comp
-- name    : SNumbers.IsMetricSurjection.norm_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:09:00.580335+00:00
-- url     : https://prove2.me/theorems/f314f107-992e-5d90-a990-1f0f40b276da
-- title:
--   Is Metric Surjection: norm comp
-- statement:
--   Pre-composition with a metric surjection preserves the operator norm:
--   `‖T ∘ Q‖ = ‖T‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L118-L141
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L118-L141

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

theorem SNumbers.IsMetricSurjection.norm_comp {Q : W →L[𝕜] X} (hQ : IsMetricSurjection Q)
    (T : X →L[𝕜] Y) : ‖T.comp Q‖ = ‖T‖ := by sorry
