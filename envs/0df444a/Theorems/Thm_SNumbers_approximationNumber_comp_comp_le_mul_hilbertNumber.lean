-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_comp_comp_le_mul_hilbertNumber
-- name    : SNumbers.approximationNumber_comp_comp_le_mul_hilbertNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:57:26.453023+00:00
-- url     : https://prove2.me/theorems/ca130e66-968a-4b4d-93be-87e1e5aaf380
-- title:
--   SNumbers: approximation Number comp comp le mul hilbert Number
-- statement:
--   **Ingredient (1) of the determinant bound.** The (S3)-type bound for the
--   Hilbert numbers: `aₙ(B ∘ S ∘ A) ≤ ‖B‖·‖A‖·hₙ(S)` for `A : ℓ₂ → X`,
--   `B : Y → ℓ₂`. Immediate from the definition of `hₙ` as a supremum of
--   ratios `aₙ(BSA)/(‖B‖‖A‖)` (`ratio_le_hilbertNumber`); the zero cases are
--   handled separately since then `B ∘ S ∘ A = 0`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L607-L620
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L607-L620

module
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_Uniqueness
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_SingularValuesFinDim
public import Definitions.Def_BasicResults_GarlingGordon
public import Definitions.Def_BasicResults_KadetsSnobar
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Definitions.Def_SNumbers_Inequalities
set_option autoImplicit true
@[expose] public section
public section
universe u
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜]
variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [CompleteSpace X] [CompleteSpace Y]
omit [CompleteSpace X] [CompleteSpace Y]

theorem SNumbers.approximationNumber_comp_comp_le_mul_hilbertNumber
    (S : X →L[𝕜] Y) (A : L2 𝕜 →L[𝕜] X) (B : Y →L[𝕜] L2 𝕜) (n : ℕ) :
    approximationNumber (B.comp (S.comp A)) n ≤ ‖B‖ * ‖A‖ * hilbertNumber S n := by sorry
