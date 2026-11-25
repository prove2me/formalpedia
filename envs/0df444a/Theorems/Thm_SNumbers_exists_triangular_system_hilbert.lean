-- Prove2me | Theorems.Thm_SNumbers_exists_triangular_system_hilbert
-- name    : SNumbers.exists_triangular_system_hilbert
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T04:28:20.046806+00:00
-- url     : https://prove2.me/theorems/3bc1cd6e-70f1-450b-8e8c-9752969c061c
-- title:
--   SNumbers: exists triangular system hilbert
-- statement:
--   Orthonormal version of the nested construction: the images `S eⱼ` are
--   pairwise orthogonal and of unit norm.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L247-L280
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Inequalities.lean#L247-L280

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
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem SNumbers.exists_triangular_system_hilbert (S : X →L[𝕜] H) {n : ℕ}
    {γ : ℝ} (hγ : 0 < γ) (hγc : γ < gelfandNumber S n) :
    ∀ m : ℕ, m ≤ n + 1 → ∃ e : Fin m → X,
      (∀ j, ‖S (e j)‖ = 1) ∧ (∀ j, ‖e j‖ ≤ 1 / γ) ∧
      (∀ i j : Fin m, i < j → inner 𝕜 (S (e i)) (S (e j)) = 0) := by sorry
