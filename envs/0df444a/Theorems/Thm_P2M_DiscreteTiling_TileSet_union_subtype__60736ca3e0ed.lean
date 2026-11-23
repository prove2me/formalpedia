-- Prove2me | Theorems.Thm_P2M_DiscreteTiling_TileSet_union_subtype__60736ca3e0ed
-- name    : P2M_DiscreteTiling_TileSet_union_subtype__60736ca3e0ed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:14:10.985411+00:00
-- url     : https://prove2.me/theorems/e95451bf-1ba6-4a49-be3a-b687f1d998e5
-- title:
--   P2 M Discrete Tiling Tile Set union subtype  60736ca3e0ed: P2 M Discrete Tiling Tile Set union subtype  60736ca3e0ed
-- statement:
--   The P2 M Discrete Tiling Tile Set union subtype  60736ca3e0ed construction uses the P2 M Discrete Tiling Tile Set union subtype  60736ca3e0ed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L114-L116
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L114-L116

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Cardinal Pointwise
variable {G X ιₚ ιₜ ιₜ' Eᵤ : Type*} [Group G] [MulAction G X] {ps : Protoset G X ιₚ}
universe u
variable {ιᵤ ιᵤ' : Type u} [EquivLike Eᵤ ιᵤ' ιᵤ]
open DiscreteTiling.TileSet

theorem P2M_DiscreteTiling_TileSet_union_subtype__60736ca3e0ed (t : TileSet ps ιₜ) (p : ιₜ → Prop) :
    ⋃ pt ∈ t.subtype p, (pt : Set X) = ⋃ (i) (_ : p i), (t i : Set X) := by sorry

alias «DiscreteTiling».«TileSet».«union_subtype'» := P2M_DiscreteTiling_TileSet_union_subtype__60736ca3e0ed
