-- Prove2me | Theorems.Thm_P2M_Csg_MatrixGame_mem_stdSimplex_comp_symm__e48fc2146e7d
-- name    : P2M_Csg_MatrixGame_mem_stdSimplex_comp_symm__e48fc2146e7d
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T22:04:41.544911+00:00
-- url     : https://prove2.me/theorems/137f4e60-6366-4a40-8c2a-0a2e942be5eb
-- title:
--   P2 M Csg Matrix Game mem std Simplex comp symm  e48fc2146e7d: P2 M Csg Matrix Game mem std Simplex comp symm  e48fc2146e7d
-- statement:
--   Mirror of `mem_stdSimplex_comp_symm`, for the column side.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L583-L586
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L583-L586

import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex
import Definitions.Def_Csg_MatrixGame
set_option autoImplicit true
open Csg
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J]
  [DecidableEq I] [DecidableEq J]
open Csg.MatrixGame
variable (G : MatrixGame I J)
variable {I' : Type*} [Fintype I'] [Nonempty I'] [DecidableEq I']
variable {J' : Type*} [Fintype J'] [Nonempty J'] [DecidableEq J']
omit [Nonempty J] [DecidableEq J] [Nonempty J'] [DecidableEq J']

theorem P2M_Csg_MatrixGame_mem_stdSimplex_comp_symm__e48fc2146e7d (e : J' ≃ J) {y' : J' → ℝ} (hy' : y' ∈ stdSimplex ℝ J') :
    y' ∘ ⇑e.symm ∈ stdSimplex ℝ J := by sorry

alias «Csg».«MatrixGame».«mem_stdSimplex_comp_symm'» := P2M_Csg_MatrixGame_mem_stdSimplex_comp_symm__e48fc2146e7d
