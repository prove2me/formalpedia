-- Prove2me | Theorems.Thm_P2M_DiscreteTiling_VarTileSetFunction_toTileSetFunction_comp__1bbb6614c81b
-- name    : P2M_DiscreteTiling_VarTileSetFunction_toTileSetFunction_comp__1bbb6614c81b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:00:56.47912+00:00
-- url     : https://prove2.me/theorems/49689e43-e3fe-434e-b0a4-a5673a349848
-- title:
--   P2 M Discrete Tiling Var Tile Set Function to Tile Set Function comp  1bbb6614c81b: P2 M Discrete Tiling Var Tile Set Function to Tile Set Function comp  1bbb6614c81b
-- statement:
--   The P2 M Discrete Tiling Var Tile Set Function to Tile Set Function comp  1bbb6614c81b construction uses the P2 M Discrete Tiling Var Tile Set Function to Tile Set Function comp  1bbb6614c81b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Basic.lean#L321-L324
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Basic.lean#L321-L324

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coeSet_sum
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sigma
public import Theorems.Thm_DiscreteTiling_TileSet_coe_sum
public import Theorems.Thm_DiscreteTiling_TileSet_mem_sum
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_one
public import Theorems.Thm_DiscreteTiling_TileSet_smul_prod_refl
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_of_isEmpty
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex
public import Theorems.Thm_DiscreteTiling_TileSet_symmetryGroup_reindex_of_bijective
attribute [local simp] DiscreteTiling.TileSet.coeSet_sigma
attribute [local simp] DiscreteTiling.TileSet.coeSet_sum
attribute [local simp] DiscreteTiling.TileSet.coe_sigma
attribute [local simp] DiscreteTiling.TileSet.coe_sum
attribute [local simp] DiscreteTiling.TileSet.mem_sum
attribute [local simp] DiscreteTiling.TileSet.smul_prod_one
attribute [local simp] DiscreteTiling.TileSet.smul_prod_refl
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_of_isEmpty
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex
attribute [local simp] DiscreteTiling.TileSet.symmetryGroup_reindex_of_bijective


set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X Y ιₚ : Type*} [Group G] [MulAction G X] [MulAction G Y]
universe u
variable {ps : Protoset G X ιₚ} {ιᵤ ιᵤ' : Type u} {ιₜ ιₜ' Eᵤ α β γ : Type*}
variable {H : Subgroup G}
variable [EquivLike Eᵤ ιᵤ' ιᵤ]
open DiscreteTiling.VarTileSetFunction
attribute [coe] toFun
attribute [simp] smul_eq

theorem P2M_DiscreteTiling_VarTileSetFunction_toTileSetFunction_comp__1bbb6614c81b (f : VarTileSetFunction Y ps α H) (f' : VarTileSetFunction Y ps β H)
    (fabg : α → β → γ) (y : Y) : (f.comp₂ f' fabg).toTileSetFunction y =
      (f.toTileSetFunction y).comp₂ (f'.toTileSetFunction y) fabg := by sorry

alias «DiscreteTiling».«VarTileSetFunction».«toTileSetFunction_comp₂» := P2M_DiscreteTiling_VarTileSetFunction_toTileSetFunction_comp__1bbb6614c81b
