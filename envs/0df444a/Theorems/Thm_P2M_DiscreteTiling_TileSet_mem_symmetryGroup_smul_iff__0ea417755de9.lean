-- Prove2me | Theorems.Thm_P2M_DiscreteTiling_TileSet_mem_symmetryGroup_smul_iff__0ea417755de9
-- name    : P2M_DiscreteTiling_TileSet_mem_symmetryGroup_smul_iff__0ea417755de9
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T05:52:32.068338+00:00
-- url     : https://prove2.me/theorems/d39ebd8d-3333-4f77-bf59-6baba3e69de5
-- title:
--   P2 M Discrete Tiling Tile Set mem symmetry Group smul iff  0ea417755de9: P2 M Discrete Tiling Tile Set mem symmetry Group smul iff  0ea417755de9
-- statement:
--   The P2 M Discrete Tiling Tile Set mem symmetry Group smul iff  0ea417755de9 construction uses the P2 M Discrete Tiling Tile Set mem symmetry Group smul iff  0ea417755de9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L409-L412
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/TileSet.lean#L409-L412

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

theorem P2M_DiscreteTiling_TileSet_mem_symmetryGroup_smul_iff__0ea417755de9 {t : TileSet ps ιₜ} {g g' : G} :
    g' ∈ (g • t).symmetryGroup ↔ g⁻¹ * g' * g ∈ t.symmetryGroup := by sorry

alias «DiscreteTiling».«TileSet».«mem_symmetryGroup_smul_iff'» := P2M_DiscreteTiling_TileSet_mem_symmetryGroup_smul_iff__0ea417755de9
