-- Prove2me | Theorems.Thm_SNumbers_L1Linf_sum_norm_le_sqrt_mul_norm
-- name    : SNumbers.L1Linf.sum_norm_le_sqrt_mul_norm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:13:47.325122+00:00
-- url     : https://prove2.me/theorems/fa9e9179-84ba-4cb8-a4a2-b02bbfc58a1b
-- title:
--   L1 Linf: sum norm le sqrt mul norm
-- statement:
--   `∑ᵢ ‖vᵢ‖ ≤ √m · ‖v‖₂` on `ℓ₂ᵐ`: the `EuclideanSpace` reading of
--   `SNumbers.sum_le_sqrt_card_mul_sqrt_sum_sq`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L212-L215
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L212-L215

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_AddOns_Approximable
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences
public import Definitions.Def_SNumbers_Examples_IdentityL1Linfty
set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
open scoped Finset

theorem SNumbers.L1Linf.sum_norm_le_sqrt_mul_norm {m : ℕ} (v : EuclideanSpace 𝕜 (Fin m)) :
    ∑ i, ‖v i‖ ≤ Real.sqrt m * ‖v‖ := by sorry
