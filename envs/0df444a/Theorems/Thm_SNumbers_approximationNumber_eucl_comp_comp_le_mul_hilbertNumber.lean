-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_eucl_comp_comp_le_mul_hilbertNumber
-- name    : SNumbers.approximationNumber_eucl_comp_comp_le_mul_hilbertNumber
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:56:37.27056+00:00
-- url     : https://prove2.me/theorems/3f558859-29fc-5d4c-86a8-e6551a515774
-- title:
--   SNumbers: approximation Number eucl comp comp le mul hilbert Number
-- statement:
--   **Ingredient (1), finite-dimensional form.** For finite factors
--   `A' : ℓ₂ⁿ⁺¹ → X`, `B' : Y → ℓ₂ⁿ⁺¹`, still `aₖ(B'∘S∘A') ≤ ‖B'‖·‖A'‖·hₖ(S)`.
--   Compose with the isometric section `ℓ₂ⁿ⁺¹ ↪ ℓ₂` (`exists_l2_section`, both
--   maps norm `≤ 1`) and apply the `ℓ₂`-form together with the (S3) ideal
--   property to drop the section maps.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L642-L674
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L642-L674

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

theorem SNumbers.approximationNumber_eucl_comp_comp_le_mul_hilbertNumber (S : X →L[𝕜] Y) (n k : ℕ)
    (A' : EuclideanSpace 𝕜 (Fin (n + 1)) →L[𝕜] X)
    (B' : Y →L[𝕜] EuclideanSpace 𝕜 (Fin (n + 1))) :
    approximationNumber (B'.comp (S.comp A')) k ≤ ‖B'‖ * ‖A'‖ * hilbertNumber S k := by sorry
