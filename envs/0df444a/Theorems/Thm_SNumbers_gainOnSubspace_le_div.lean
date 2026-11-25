-- Prove2me | Theorems.Thm_SNumbers_gainOnSubspace_le_div
-- name    : SNumbers.gainOnSubspace_le_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T00:51:40.293877+00:00
-- url     : https://prove2.me/theorems/140947e8-9f2a-4d3d-a1b6-71ac09e5de5d
-- title:
--   SNumbers: gain On Subspace le div
-- statement:
--   Pointwise upper bound: every nonzero `x ∈ M` upper-bounds the gain.
--
--   Source: https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L89-L92
-- source:
--   https://github.com/mario-ullrich/Lean-SNumbers/blob/b3f7bb9524bafdfa5a8fba877fef02ea5a950ebd/SNumbers/Bernstein.lean#L89-L92

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

theorem SNumbers.gainOnSubspace_le_div {S : X →L[𝕜] Y} {M : Submodule 𝕜 X} {x : X}
    (hx_mem : x ∈ M) (hx_ne : x ≠ 0) :
    gainOnSubspace S M ≤ ‖S x‖ / ‖x‖ := by sorry
