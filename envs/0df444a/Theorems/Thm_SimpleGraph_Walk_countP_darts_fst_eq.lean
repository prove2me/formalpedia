-- Prove2me | Theorems.Thm_SimpleGraph_Walk_countP_darts_fst_eq
-- name    : SimpleGraph.Walk.countP_darts_fst_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:38:58.097942+00:00
-- url     : https://prove2.me/theorems/3ae1a684-2b4a-4d9d-bb13-94c4b76d6ea8
-- title:
--   Walk: count P darts fst eq
-- statement:
--   En un paseo cerrado salen de cada vértice tantos dardos como entran.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Orientation.lean#L48-L51
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Orientation.lean#L48-L51

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

theorem SimpleGraph.Walk.countP_darts_fst_eq {u : V} (p : G.Walk u u) (v : V) :
    p.darts.countP (fun d => d.fst = v) = p.darts.countP (fun d => d.snd = v) := by sorry
