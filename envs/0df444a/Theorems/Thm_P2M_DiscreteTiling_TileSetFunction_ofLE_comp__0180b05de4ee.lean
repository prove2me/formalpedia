-- Prove2me | Theorems.Thm_P2M_DiscreteTiling_TileSetFunction_ofLE_comp__0180b05de4ee
-- name    : P2M_DiscreteTiling_TileSetFunction_ofLE_comp__0180b05de4ee
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:00:20.524099+00:00
-- url     : https://prove2.me/theorems/6f9e6f86-5654-400a-8605-f1ac9a4cf3cb
-- title:
--   P2 M Discrete Tiling Tile Set Function of LE comp  0180b05de4ee: P2 M Discrete Tiling Tile Set Function of LE comp  0180b05de4ee
-- statement:
--   The P2 M Discrete Tiling Tile Set Function of LE comp  0180b05de4ee construction uses the P2 M Discrete Tiling Tile Set Function of LE comp  0180b05de4ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Basic.lean#L180-L182
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Basic.lean#L180-L182

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
open DiscreteTiling.TileSetFunction
attribute [coe] toFun
attribute [simp] smul_eq

theorem P2M_DiscreteTiling_TileSetFunction_ofLE_comp__0180b05de4ee (f : TileSetFunction ps α H) (f' : TileSetFunction ps β H) (fabg : α → β → γ)
    {H' : Subgroup G} (h : H' ≤ H) : (f.comp₂ f' fabg).ofLE h = (f.ofLE h).comp₂ (f'.ofLE h) fabg := by sorry

alias «DiscreteTiling».«TileSetFunction».«ofLE_comp₂» := P2M_DiscreteTiling_TileSetFunction_ofLE_comp__0180b05de4ee
