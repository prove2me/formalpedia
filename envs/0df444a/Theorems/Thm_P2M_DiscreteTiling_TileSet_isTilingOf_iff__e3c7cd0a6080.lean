-- Prove2me | Theorems.Thm_P2M_DiscreteTiling_TileSet_isTilingOf_iff__e3c7cd0a6080
-- name    : P2M_DiscreteTiling_TileSet_isTilingOf_iff__e3c7cd0a6080
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T06:09:22.817192+00:00
-- url     : https://prove2.me/theorems/e6dbbd2f-567d-4637-b5d3-c0c35b5fb53e
-- title:
--   P2 M Discrete Tiling Tile Set is Tiling Of iff  e3c7cd0a6080: P2 M Discrete Tiling Tile Set is Tiling Of iff  e3c7cd0a6080
-- statement:
--   The P2 M Discrete Tiling Tile Set is Tiling Of iff  e3c7cd0a6080 construction uses the P2 M Discrete Tiling Tile Set is Tiling Of iff  e3c7cd0a6080 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L50-L52
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L50-L52

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Disjoint
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Tiling
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ : Type*}
open DiscreteTiling.TileSet

theorem P2M_DiscreteTiling_TileSet_isTilingOf_iff__e3c7cd0a6080 {t : TileSet ps ιₜ} {s : Set X} : t.IsTilingOf s ↔
    t.Disjoint ∧ t.UnionEq s := by sorry

alias «DiscreteTiling».«TileSet».«isTilingOf_iff'» := P2M_DiscreteTiling_TileSet_isTilingOf_iff__e3c7cd0a6080
