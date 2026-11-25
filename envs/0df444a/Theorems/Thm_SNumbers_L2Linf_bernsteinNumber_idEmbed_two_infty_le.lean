-- Prove2me | Theorems.Thm_SNumbers_L2Linf_bernsteinNumber_idEmbed_two_infty_le
-- name    : SNumbers.L2Linf.bernsteinNumber_idEmbed_two_infty_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:43:06.254187+00:00
-- url     : https://prove2.me/theorems/242d73e9-f7a9-49e3-bfb5-dd459c9ad435
-- title:
--   L2 Linf: bernstein Number id Embed two infty le
-- statement:
--   **Bernstein numbers of `ℓ₂ᴺ → ℓ∞ᴺ`**: `bₙ(id : ℓ₂ᴺ → ℓ∞ᴺ) ≤ 1/√(n+1)`. Every
--   `(n+1)`-dimensional subspace contains a flat vector `x` (`exists_flat_vector`), with
--   `‖x‖_∞ ≤ 1` and `‖x‖₂ ≥ √(n+1)`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L78-L107
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L78-L107

module
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Operator.Prod
public import Definitions.Def_SNumbers_Examples_IdentityL2Linfty
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal ComplexConjugate
open ContinuousLinearMap
open SNumbers SNumbers.L2Linf
variable {𝕜 : Type u} [RCLike 𝕜]

theorem SNumbers.L2Linf.bernsteinNumber_idEmbed_two_infty_le (N n : ℕ) :
    bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := N) ∞ 2) n ≤ 1 / Real.sqrt (n + 1) := by sorry
