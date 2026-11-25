-- Prove2me | Theorems.Thm_SNumbers_deviationFromSubspace_add_le
-- name    : SNumbers.deviationFromSubspace_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:10:24.018847+00:00
-- url     : https://prove2.me/theorems/ecba2aa5-3ad1-4e92-9997-04c3043c496d
-- title:
--   SNumbers: deviation From Subspace add le
-- statement:
--   The triangle inequality for quotient norms:
--   `‖π_V ∘ (S + T)‖ ≤ ‖π_V ∘ S‖ + ‖π_V ∘ T‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L273-L278
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Kolmogorov.lean#L273-L278

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_QuotientMapNorms
public import Mathlib.Analysis.Normed.Module.RieszLemma
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Kolmogorov
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

theorem SNumbers.deviationFromSubspace_add_le (S T : X →L[𝕜] Y) (V : Submodule 𝕜 Y) :
    deviationFromSubspace (S + T) V ≤
      deviationFromSubspace S V + deviationFromSubspace T V := by sorry
