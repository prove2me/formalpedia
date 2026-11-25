-- Prove2me | Theorems.Thm_SNumbers_L2Linf_sqrt_le_norm_toLp_two
-- name    : SNumbers.L2Linf.sqrt_le_norm_toLp_two
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T02:59:11.535841+00:00
-- url     : https://prove2.me/theorems/905fde4b-1297-427c-8c1a-79f0e92c87c7
-- title:
--   L2 Linf: sqrt le norm to Lp two
-- statement:
--   A vector with at least `k` coordinates of modulus `1` has `ℓ₂`-norm at least `√k`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L60-L73
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL2Linfty.lean#L60-L73

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

theorem SNumbers.L2Linf.sqrt_le_norm_toLp_two {N k : ℕ} (w : Fin N → 𝕜)
    (hk : k ≤ (Finset.univ.filter fun i => ‖w i‖ = 1).card) :
    Real.sqrt k ≤ ‖(WithLp.toLp 2 w : PiLp 2 (fun _ : Fin N => 𝕜))‖ := by sorry
