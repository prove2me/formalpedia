-- Prove2me | Theorems.Thm_P2M_DiscreteTiling_TileSet_unionEqUniv_iff__13676d5e172c
-- name    : P2M_DiscreteTiling_TileSet_unionEqUniv_iff__13676d5e172c
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T06:09:15.853177+00:00
-- url     : https://prove2.me/theorems/eec5b5bd-f390-494f-895c-254a37a079b5
-- title:
--   P2 M Discrete Tiling Tile Set union Eq Univ iff  13676d5e172c: P2 M Discrete Tiling Tile Set union Eq Univ iff  13676d5e172c
-- statement:
--   The P2 M Discrete Tiling Tile Set union Eq Univ iff  13676d5e172c construction uses the P2 M Discrete Tiling Tile Set union Eq Univ iff  13676d5e172c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Union.lean#L97-L99
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Union.lean#L97-L99

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Union
set_option autoImplicit false
@[expose] public section
public section
noncomputable section
open DiscreteTiling
open Function
open scoped Pointwise
variable {G X ιₚ : Type*} [Group G] [MulAction G X]
variable {ps : Protoset G X ιₚ} {ιₜ ιₜ' : Type*}
open DiscreteTiling.TileSet

theorem P2M_DiscreteTiling_TileSet_unionEqUniv_iff__13676d5e172c {t : TileSet ps ιₜ} :
    t.UnionEqUniv ↔ (⋃ pt ∈ t, (pt : Set X)) = Set.univ := by sorry

alias «DiscreteTiling».«TileSet».«unionEqUniv_iff'» := P2M_DiscreteTiling_TileSet_unionEqUniv_iff__13676d5e172c
