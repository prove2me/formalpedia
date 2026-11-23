-- Prove2me | Theorems.Thm_P2M_DiscreteTiling_TileSet_exists_smul_eq_of_mem_symmetryGroup__3557f4183e3f
-- name    : P2M_DiscreteTiling_TileSet_exists_smul_eq_of_mem_symmetryGroup__3557f4183e3f
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:52:50.943276+00:00
-- url     : https://prove2.me/theorems/ec5e3e50-f6c7-47ce-b87b-ed6ef2e32603
-- title:
--   P2 M Discrete Tiling Tile Set exists smul eq of mem symmetry Group  3557f4183e3f: P2 M Discrete Tiling Tile Set exists smul eq of mem symmetry Group  3557f4183e3f
-- statement:
--   If `g` is in the symmetry group, every tile in `t` is the image under `g` of some tile in
--   `t`.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L349-L353
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L349-L353

module
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Combinatorics.Tiling.Tile
public import Mathlib.GroupTheory.GroupAction.Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ι ιₜ ιₜ' ιₜ'' ιₜ''' E E' F : Type*} {ιₜι ιₜ'ι : ι → Type*}
variable [EquivLike E ιₜ' ιₜ] [EquivLike E' ιₜ'' ιₜ'] [FunLike F ιₜ' ιₜ] [EmbeddingLike F ιₜ' ιₜ]
open DiscreteTiling.TileSet
attribute [coe] tiles

theorem P2M_DiscreteTiling_TileSet_exists_smul_eq_of_mem_symmetryGroup__3557f4183e3f {t : TileSet ps ιₜ} {g : G} (i : ιₜ)
    (hg : g ∈ t.symmetryGroup) : ∃ j, g • (t j) = t i := by sorry

alias «DiscreteTiling».«TileSet».«exists_smul_eq_of_mem_symmetryGroup'» := P2M_DiscreteTiling_TileSet_exists_smul_eq_of_mem_symmetryGroup__3557f4183e3f
