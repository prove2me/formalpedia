-- Prove2me | Theorems.Thm_P2M_DiscreteTiling_TileSet_finiteLocalComplexity_iff__f2fecaa7276b
-- name    : P2M_DiscreteTiling_TileSet_finiteLocalComplexity_iff__f2fecaa7276b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T06:17:31.341164+00:00
-- url     : https://prove2.me/theorems/79871ce1-c66f-4b03-bad5-1c6498461d10
-- title:
--   P2 M Discrete Tiling Tile Set finite Local Complexity iff  f2fecaa7276b: P2 M Discrete Tiling Tile Set finite Local Complexity iff  f2fecaa7276b
-- statement:
--   The definition of `FiniteLocalComplexity` in term of finiteness for pairs involving a point
--   rather than a singleton set of that point.
--
--   Source: https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/FiniteLocalComplexity.lean#L104-L129
-- source:
--   https://github.com/jsm28/AperiodicMonotilesLean/blob/b98c45401bd7d9017175ab2dc20cc8759e2b7c4b/AM/Mathlib/Combinatorics/Tiling/Function/FiniteLocalComplexity.lean#L104-L129

module
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_Basic
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Patch
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_TileSetCard
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Definitions.Def_AM_Mathlib_Combinatorics_Tiling_Function_FiniteLocalComplexity
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

theorem P2M_DiscreteTiling_TileSet_finiteLocalComplexity_iff__f2fecaa7276b {H : Subgroup G} {t : TileSet ps ιₜ} :
    t.FiniteLocalComplexity H ↔
      (Set.range (fun x ↦ Quotient.mk (MulAction.orbitRel H (X × TileSetCard ps))
        (x, (t.patch {x}).card))).Finite := by sorry

alias «DiscreteTiling».«TileSet».«finiteLocalComplexity_iff'» := P2M_DiscreteTiling_TileSet_finiteLocalComplexity_iff__f2fecaa7276b
