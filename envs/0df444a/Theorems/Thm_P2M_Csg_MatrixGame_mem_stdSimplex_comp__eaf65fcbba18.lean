-- Prove2me | Theorems.Thm_P2M_Csg_MatrixGame_mem_stdSimplex_comp__eaf65fcbba18
-- name    : P2M_Csg_MatrixGame_mem_stdSimplex_comp__eaf65fcbba18
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:04:45.362798+00:00
-- url     : https://prove2.me/theorems/32a691c4-5018-47ee-9539-aedf48d7d46a
-- title:
--   P2 M Csg Matrix Game mem std Simplex comp  eaf65fcbba18: P2 M Csg Matrix Game mem std Simplex comp  eaf65fcbba18
-- statement:
--   Mirror of `mem_stdSimplex_comp`, for the column side.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L590-L593
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Csg/MatrixGame.lean#L590-L593

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

theorem P2M_Csg_MatrixGame_mem_stdSimplex_comp__eaf65fcbba18 (e : J' ≃ J) {y : J → ℝ} (hy : y ∈ stdSimplex ℝ J) :
    y ∘ ⇑e ∈ stdSimplex ℝ J' := by sorry

alias «Csg».«MatrixGame».«mem_stdSimplex_comp'» := P2M_Csg_MatrixGame_mem_stdSimplex_comp__eaf65fcbba18
