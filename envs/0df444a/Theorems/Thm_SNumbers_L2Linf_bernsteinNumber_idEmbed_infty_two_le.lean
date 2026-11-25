-- Prove2me | Theorems.Thm_SNumbers_L2Linf_bernsteinNumber_idEmbed_infty_two_le
-- name    : SNumbers.L2Linf.bernsteinNumber_idEmbed_infty_two_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:48:51.068724+00:00
-- url     : https://prove2.me/theorems/fdaeb8eb-56c0-5feb-ba73-d1e1f5bc8267
-- title:
--   L2 Linf: bernstein Number id Embed infty two le
-- statement:
--   **Bernstein numbers of `ℓ∞ᴺ → ℓ₂ᴺ`**: `bₙ(id : ℓ∞ᴺ → ℓ₂ᴺ) ≤ √(N/(n+1))`. On an
--   `(n+1)`-dimensional subspace with gain `c`, every coordinate `k` gives `c² sₖ ≤ 1`, where
--   `sₖ = ∑ᵢ |vᵢ(k)|²` for an orthonormal basis `(vᵢ)` (`exists_mem_apply_eq_norm_sq`), and
--   `∑ₖ sₖ = n + 1` (`sum_sum_norm_sq_apply`).
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L144-L207
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L144-L207

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

theorem SNumbers.L2Linf.bernsteinNumber_idEmbed_infty_two_le (N n : ℕ) :
    bernsteinNumber (idEmbed (𝕜 := 𝕜) (m := N) 2 ∞) n ≤ Real.sqrt (N / (n + 1)) := by sorry
