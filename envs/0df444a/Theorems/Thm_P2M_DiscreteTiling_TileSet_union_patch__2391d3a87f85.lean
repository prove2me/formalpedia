-- Prove2me | Theorems.Thm_P2M_DiscreteTiling_TileSet_union_patch__2391d3a87f85
-- name    : P2M_DiscreteTiling_TileSet_union_patch__2391d3a87f85
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:17:03.320666+00:00
-- url     : https://prove2.me/theorems/313e7935-71f0-40bc-9d74-2b613c217ab9
-- title:
--   P2 M Discrete Tiling Tile Set union patch  2391d3a87f85: P2 M Discrete Tiling Tile Set union patch  2391d3a87f85
-- statement:
--   The P2 M Discrete Tiling Tile Set union patch  2391d3a87f85 construction uses the P2 M Discrete Tiling Tile Set union patch  2391d3a87f85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L227-L229
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Patch.lean#L227-L229

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

theorem P2M_DiscreteTiling_TileSet_union_patch__2391d3a87f85 (t : TileSet ps ιₜ) (s : Set X) :
    ⋃ pt ∈ t.patch s, (pt : Set X) = ⋃ (i) (_ : (s ∩ t i).Nonempty), (t i : Set X) := by sorry

alias «DiscreteTiling».«TileSet».«union_patch'» := P2M_DiscreteTiling_TileSet_union_patch__2391d3a87f85
