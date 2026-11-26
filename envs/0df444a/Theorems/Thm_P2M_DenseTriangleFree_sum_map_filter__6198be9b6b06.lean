-- Prove2me | Theorems.Thm_P2M_DenseTriangleFree_sum_map_filter__6198be9b6b06
-- name    : P2M_DenseTriangleFree_sum_map_filter__6198be9b6b06
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:47:08.505085+00:00
-- url     : https://prove2.me/theorems/5730e41a-647c-4287-954f-4afdf6f5382c
-- title:
--   P2 M Dense Triangle Free sum map filter  6198be9b6b06: P2 M Dense Triangle Free sum map filter  6198be9b6b06
-- statement:
--   The P2 M Dense Triangle Free sum map filter  6198be9b6b06 construction uses the P2 M Dense Triangle Free sum map filter  6198be9b6b06 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Heavy.lean#L142-L147
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Heavy.lean#L142-L147

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Heavy
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph

theorem P2M_DenseTriangleFree_sum_map_filter__6198be9b6b06 {p : ℕ → Prop} [DecidablePred p] (L : List ℕ) (g : ℕ → ℕ) :
    ((L.filter fun i => decide (p i)).map g).sum =
      (L.map fun i => if p i then g i else 0).sum := by sorry

alias «DenseTriangleFree».«sum_map_filter'» := P2M_DenseTriangleFree_sum_map_filter__6198be9b6b06
