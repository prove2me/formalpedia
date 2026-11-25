-- Prove2me | Theorems.Thm_SNumbers_deviationFromRestriction_comp_comp_comap_le
-- name    : SNumbers.deviationFromRestriction_comp_comp_comap_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:28:31.451283+00:00
-- url     : https://prove2.me/theorems/5a27caa8-bb62-5c83-a7eb-1e8511e31b15
-- title:
--   SNumbers: deviation From Restriction comp comp comap le
-- statement:
--   Per-subspace (S3) bound:
--   `deviation(B ∘ S ∘ A, M.comap A) ≤ ‖B‖ * ‖A‖ * deviation(S, M)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L423-L446
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Gelfand.lean#L423-L446

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_Gelfand
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

theorem SNumbers.deviationFromRestriction_comp_comp_comap_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (M : Submodule 𝕜 X) :
    deviationFromRestriction (B.comp (S.comp A))
        (M.comap (A : W →ₗ[𝕜] X))
      ≤ ‖B‖ * ‖A‖ * deviationFromRestriction S M := by sorry
