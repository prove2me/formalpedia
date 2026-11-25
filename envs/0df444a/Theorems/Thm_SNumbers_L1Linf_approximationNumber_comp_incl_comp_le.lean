-- Prove2me | Theorems.Thm_SNumbers_L1Linf_approximationNumber_comp_incl_comp_le
-- name    : SNumbers.L1Linf.approximationNumber_comp_incl_comp_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T05:16:09.224834+00:00
-- url     : https://prove2.me/theorems/b4ee4343-709d-53a4-8933-494ce07f6871
-- title:
--   L1 Linf: approximation Number comp incl comp le
-- statement:
--   **The key estimate.** `aₙ(B I A) ≤ ‖A‖ ‖B‖ / (n+1)` for *all* bounded
--   `A : ℓ₂ → ℓ₁` and `B : ℓ_∞ → ℓ₂`.
--
--   The truncation error is handled with the subadditivity of the approximation
--   numbers: `aₙ(T) ≤ aₙ(Tₘ) + ‖T - Tₘ‖`, where `‖T - Tₘ‖ ≤ ‖B‖ δ` as soon as
--   `‖rowⱼ‖ ≤ δ` for all `j ≥ m`, which holds eventually since `∑ⱼ ‖rowⱼ‖² < ∞`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L607-L661
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Examples/IdentityL1Linfty.lean#L607-L661

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
variable (A : L2 𝕜 →L[𝕜] L1 𝕜) (B : Linf 𝕜 →L[𝕜] L2 𝕜)

theorem SNumbers.L1Linf.approximationNumber_comp_incl_comp_le (n : ℕ) :
    approximationNumber (B.comp ((incl : L1 𝕜 →L[𝕜] Linf 𝕜).comp A)) n
      ≤ ‖A‖ * ‖B‖ / (n + 1) := by sorry
