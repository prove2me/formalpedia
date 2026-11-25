-- Prove2me | Theorems.Thm_SNumbers_approximationNumber_le_sqrt_mul_deviationFromRestriction
-- name    : SNumbers.approximationNumber_le_sqrt_mul_deviationFromRestriction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:54:35.685069+00:00
-- url     : https://prove2.me/theorems/38fa5696-ad7a-46ce-a282-3b2e527c30a4
-- title:
--   SNumbers: approximation Number le sqrt mul deviation From Restriction
-- statement:
--   **Gelfand half, per subspace.** For a closed `M ⊆ X` of codimension
--   `≤ n`, `aₙ(S) ≤ (1 + √n)·‖S|_M‖`. The approximant is `L := S ∘ P` for the
--   Garling–Gordon projection `P` with kernel `M`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L437-L492
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L437-L492

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

theorem SNumbers.approximationNumber_le_sqrt_mul_deviationFromRestriction
    (S : X →L[𝕜] Y) {n : ℕ} {M : Submodule 𝕜 X}
    (hM_closed : IsClosed (M : Set X))
    (hM_codim : Module.rank 𝕜 (X ⧸ M) ≤ (n : Cardinal)) :
    approximationNumber S n ≤ (1 + Real.sqrt n) * deviationFromRestriction S M := by sorry
