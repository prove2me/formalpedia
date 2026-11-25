-- Prove2me | Theorems.Thm_SimpleGraph_card_image_edge_filter
-- name    : SimpleGraph.card_image_edge_filter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:38:24.797296+00:00
-- url     : https://prove2.me/theorems/f6718444-68f2-4b97-9b94-73cb8f9b0f72
-- title:
--   Simple Graph: card image edge filter
-- statement:
--   Las aristas de un conjunto de dardos con a lo más un dardo por arista, contadas en `v`.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Orientation.lean#L70-L96
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Orientation.lean#L70-L96

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

theorem SimpleGraph.card_image_edge_filter {Ds : Finset G.Dart} (hinj : EdgeInj Ds) (v : V) :
    ((Ds.image Dart.edge).filter (v ∈ ·)).card =
      (Ds.filter fun d => d.fst = v).card + (Ds.filter fun d => d.snd = v).card := by sorry
