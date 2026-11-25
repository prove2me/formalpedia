-- Prove2me | Theorems.Thm_SNumbers_deviationFromSubspace_comp_metricSurjection
-- name    : SNumbers.deviationFromSubspace_comp_metricSurjection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:09:36.222267+00:00
-- url     : https://prove2.me/theorems/8ce25ceb-2883-4d79-9893-f740cfd65d61
-- title:
--   SNumbers: deviation From Subspace comp metric Surjection
-- statement:
--   The quotient-norm defining `dₙ` is preserved by pre-composition with a
--   metric surjection: `‖π_V ∘ (S ∘ Q)‖ = ‖π_V ∘ S‖`.
--
--   This is just `IsMetricSurjection.norm_comp` applied to `T = π_V ∘ S`, but we
--   **inline** that argument with `T` abstracted by `set`: applying the generic
--   lemma directly forces the elaborator to re-infer the quotient instances
--   `NormedSpace 𝕜 (Y ⧸ V)` through a metavariable, which sends `whnf` into a
--   runaway search. With `T` opaque the same proof goes through at once.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L238-L264
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Injectivity.lean#L238-L264

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

theorem SNumbers.deviationFromSubspace_comp_metricSurjection {Q : W →L[𝕜] X}
    (hQ : IsMetricSurjection Q) (S : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    deviationFromSubspace (S.comp Q) V = deviationFromSubspace S V := by sorry
