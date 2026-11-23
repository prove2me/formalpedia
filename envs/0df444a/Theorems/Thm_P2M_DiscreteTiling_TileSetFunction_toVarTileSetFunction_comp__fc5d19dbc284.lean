-- Prove2me | Theorems.Thm_P2M_DiscreteTiling_TileSetFunction_toVarTileSetFunction_comp__fc5d19dbc284
-- name    : P2M_DiscreteTiling_TileSetFunction_toVarTileSetFunction_comp__fc5d19dbc284
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:01:04.38674+00:00
-- url     : https://prove2.me/theorems/9ab9c8e4-d5f8-4c77-bd7f-2702aaec0551
-- title:
--   P2 M Discrete Tiling Tile Set Function to Var Tile Set Function comp  fc5d19dbc284: P2 M Discrete Tiling Tile Set Function to Var Tile Set Function comp  fc5d19dbc284
-- statement:
--   The P2 M Discrete Tiling Tile Set Function to Var Tile Set Function comp  fc5d19dbc284 construction uses the P2 M Discrete Tiling Tile Set Function to Var Tile Set Function comp  fc5d19dbc284 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Basic.lean#L351-L354
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Basic.lean#L351-L354

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSet
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
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
variable (Y)

theorem P2M_DiscreteTiling_TileSetFunction_toVarTileSetFunction_comp__fc5d19dbc284 (f : TileSetFunction ps α H) (f' : TileSetFunction ps β H)
    (fabg : α → β → γ) : (f.comp₂ f' fabg).toVarTileSetFunction Y =
      (f.toVarTileSetFunction Y).comp₂ (f'.toVarTileSetFunction Y) fabg := by sorry

alias «DiscreteTiling».«TileSetFunction».«toVarTileSetFunction_comp₂» := P2M_DiscreteTiling_TileSetFunction_toVarTileSetFunction_comp__fc5d19dbc284
