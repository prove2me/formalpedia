-- Prove2me | Theorems.Thm_SNumbers_le_gainOnSubspace
-- name    : SNumbers.le_gainOnSubspace
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:54:04.596815+00:00
-- url     : https://prove2.me/theorems/26359121-0cf7-43e3-b062-62150d4e09ea
-- title:
--   SNumbers: le gain On Subspace
-- statement:
--   Lower bound on the gain: if every nonzero `x ∈ M` satisfies
--   `c ≤ ‖S x‖/‖x‖`, then `c ≤ gainOnSubspace S M`.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L96-L101
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L96-L101

module
public import Definitions.Def_SNumbers_ContinuousLinearMapRank
public import Definitions.Def_SNumbers_Injectivity
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Definitions.Def_SNumbers_Bernstein
set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped Cardinal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

theorem SNumbers.le_gainOnSubspace {S : X →L[𝕜] Y} {M : Submodule 𝕜 X} (hM : M ≠ ⊥)
    {c : ℝ} (h : ∀ x ∈ M, x ≠ 0 → c ≤ ‖S x‖ / ‖x‖) :
    c ≤ gainOnSubspace S M := by sorry
