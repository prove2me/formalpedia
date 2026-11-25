-- Prove2me | Theorems.Thm_SNumbers_L2Linf_idEmbed_two_infty_comp_idEmbed_infty_two
-- name    : SNumbers.L2Linf.idEmbed_two_infty_comp_idEmbed_infty_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:59:12.806571+00:00
-- url     : https://prove2.me/theorems/dfdd742e-dc15-5ef8-9f93-8a64ddbe5474
-- title:
--   L2 Linf: id Embed two infty comp id Embed infty two
-- statement:
--   `ℓ₂ᴺ → ℓ∞ᴺ → ℓ₂ᴺ` is the identity of `ℓ₂ᴺ`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L212-L216
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L212-L216

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

theorem SNumbers.L2Linf.idEmbed_two_infty_comp_idEmbed_infty_two (N : ℕ) :
    (idEmbed (𝕜 := 𝕜) (m := N) 2 ∞).comp (idEmbed ∞ 2) =
      ContinuousLinearMap.id 𝕜 (PiLp 2 (fun _ : Fin N => 𝕜)) := by sorry
