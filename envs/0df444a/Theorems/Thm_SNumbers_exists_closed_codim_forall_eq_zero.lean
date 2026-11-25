-- Prove2me | Theorems.Thm_SNumbers_exists_closed_codim_forall_eq_zero
-- name    : SNumbers.exists_closed_codim_forall_eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T04:27:54.70117+00:00
-- url     : https://prove2.me/theorems/2dad86ab-cccf-5d6c-a31c-2413e9db7c67
-- title:
--   SNumbers: exists closed codim forall eq zero
-- statement:
--   The common kernel `{x | ∀ i, gᵢ(S x) = 0}` of `k` continuous functionals `gᵢ ∘ S` is a
--   closed subspace of codimension `≤ k` (kernel of `x ↦ (gᵢ(S x))ᵢ : X → 𝕜ᵏ`). Used by the
--   oracles in `SNumbers.MaxDifference`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L178-L190
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L178-L190

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

theorem SNumbers.exists_closed_codim_forall_eq_zero (S : X →L[𝕜] Y) {k : ℕ}
    (g : Fin k → (Y →L[𝕜] 𝕜)) :
    ∃ M : Submodule 𝕜 X, IsClosed (M : Set X) ∧
      Module.rank 𝕜 (X ⧸ M) ≤ (k : Cardinal) ∧ (∀ x ∈ M, ∀ i, g i (S x) = 0) := by sorry
