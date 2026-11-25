-- Prove2me | Theorems.Thm_SNumbers_hilbertNumber_comp_comp_le
-- name    : SNumbers.hilbertNumber_comp_comp_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:40:36.383743+00:00
-- url     : https://prove2.me/theorems/20cb11d0-5c99-42dd-b6e1-b73f9d9daa0e
-- title:
--   SNumbers: hilbert Number comp comp le
-- statement:
--   (S3) `h_n (B ∘ S ∘ A) ≤ ‖B‖ * h_n S * ‖A‖`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L172-L209
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Hilbert.lean#L172-L209

module
public import Definitions.Def_SNumbers_Approximation
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Definitions.Def_SNumbers_Hilbert
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y W Z : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.hilbertNumber_comp_comp_le (A₀ : W →L[𝕜] X) (S : X →L[𝕜] Y) (B₀ : Y →L[𝕜] Z) (n : ℕ) :
    hilbertNumber (B₀.comp (S.comp A₀)) n ≤ ‖B₀‖ * hilbertNumber S n * ‖A₀‖ := by sorry
