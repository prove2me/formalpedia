-- Prove2me | Theorems.Thm_SimpleGraph_Walk_countP_darts_fst_add
-- name    : SimpleGraph.Walk.countP_darts_fst_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:38:31.331081+00:00
-- url     : https://prove2.me/theorems/fb450012-0289-5143-91ee-bfd68232e02e
-- title:
--   Walk: count P darts fst add
-- statement:
--   En un paseo de `u` a `w`, los dardos que salen de `v` y los que entran a `v` difieren sólo
--   en los extremos.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Orientation.lean#L35-L44
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Orientation.lean#L35-L44

module
public import Definitions.Def_Euler_Trail
public import Definitions.Def_Euler_Orientation
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
omit [Fintype V] [DecidableRel G.Adj]

theorem SimpleGraph.Walk.countP_darts_fst_add {u w : V} (p : G.Walk u w) (v : V) :
    p.darts.countP (fun d => d.fst = v) + (if w = v then 1 else 0) =
      p.darts.countP (fun d => d.snd = v) + (if u = v then 1 else 0) := by sorry
