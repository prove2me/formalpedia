-- Prove2me | Theorems.Thm_P2M_MatchingPolytope_Multi_gcut_subset_shrinkF__d7b6c02936a8
-- name    : P2M_MatchingPolytope_Multi_gcut_subset_shrinkF__d7b6c02936a8
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T23:25:22.577047+00:00
-- url     : https://prove2.me/theorems/98651daf-b2a0-4c1d-9765-07c7314e298b
-- title:
--   P2 M Matching Polytope Multi gcut subset shrink F  d7b6c02936a8: P2 M Matching Polytope Multi gcut subset shrink F  d7b6c02936a8
-- statement:
--   The P2 M Matching Polytope Multi gcut subset shrink F  d7b6c02936a8 construction uses the P2 M Matching Polytope Multi gcut subset shrink F  d7b6c02936a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L167-L172
-- source:
--   https://github.com/jtraverso/edmonds-matching-polytope/blob/6198b8314ac88a5638120fcf15d5b58c024caaab/MatchingPolytope/Glue.lean#L167-L172

module
public import Definitions.Def_MatchingPolytope_Shrink
public import Definitions.Def_MatchingPolytope_Glue
set_option autoImplicit true
@[expose] public section
public section
open MatchingPolytope MatchingPolytope.Multi
open Finset
variable {V E : Type*}
variable {ends : E → Sym2 V} {W : Finset V} {F : Finset E}
variable [DecidableEq V]

theorem P2M_MatchingPolytope_Multi_gcut_subset_shrinkF__d7b6c02936a8 (S : Finset V) :
    gcut ends F S ⊆ shrinkF ends F (W \ S) := by sorry

alias «MatchingPolytope».«Multi».«gcut_subset_shrinkF'» := P2M_MatchingPolytope_Multi_gcut_subset_shrinkF__d7b6c02936a8
