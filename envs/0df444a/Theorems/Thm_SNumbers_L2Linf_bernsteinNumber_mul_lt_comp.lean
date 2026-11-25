-- Prove2me | Theorems.Thm_SNumbers_L2Linf_bernsteinNumber_mul_lt_comp
-- name    : SNumbers.L2Linf.bernsteinNumber_mul_lt_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T03:00:06.053628+00:00
-- url     : https://prove2.me/theorems/092d2e98-55cb-50bd-917f-a6feecc682e6
-- title:
--   L2 Linf: bernstein Number mul lt comp
-- statement:
--   **The counterexample to multiplicativity.** For `T = id : ℓ₂³ → ℓ∞³` and
--   `S = id : ℓ∞³ → ℓ₂³`, `b₁(S) · b₁(T) < b₂(S ∘ T) = 1`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L220-L238
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L220-L238

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

theorem SNumbers.L2Linf.bernsteinNumber_mul_lt_comp :
    bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 3) 2 ∞) 1 *
        bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := 3) ∞ 2) 1 <
      bernsteinNumber ((idEmbed (𝕜 := 𝕜) (m := 3) 2 ∞).comp (idEmbed ∞ 2)) (1 + 1) := by sorry
