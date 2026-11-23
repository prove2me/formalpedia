-- Prove2me | Theorems.Thm_P2M_DiscreteTiling_TileSet_isTiling_iff__33c4d8525e7c
-- name    : P2M_DiscreteTiling_TileSet_isTiling_iff__33c4d8525e7c
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:09:41.414146+00:00
-- url     : https://prove2.me/theorems/0ab236a4-f43f-40cd-ad42-5537d09842ff
-- title:
--   P2 M Discrete Tiling Tile Set is Tiling iff  33c4d8525e7c: P2 M Discrete Tiling Tile Set is Tiling iff  33c4d8525e7c
-- statement:
--   The P2 M Discrete Tiling Tile Set is Tiling iff  33c4d8525e7c construction uses the P2 M Discrete Tiling Tile Set is Tiling iff  33c4d8525e7c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L90-L91
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/Tiling.lean#L90-L91

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

theorem P2M_DiscreteTiling_TileSet_isTiling_iff__33c4d8525e7c {t : TileSet ps ιₜ} : t.IsTiling ↔ t.Disjoint ∧ t.UnionEqUniv := by sorry

alias «DiscreteTiling».«TileSet».«isTiling_iff'» := P2M_DiscreteTiling_TileSet_isTiling_iff__33c4d8525e7c
