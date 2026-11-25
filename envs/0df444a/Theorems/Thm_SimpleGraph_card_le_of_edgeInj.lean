-- Prove2me | Theorems.Thm_SimpleGraph_card_le_of_edgeInj
-- name    : SimpleGraph.card_le_of_edgeInj
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T17:38:59.995867+00:00
-- url     : https://prove2.me/theorems/fc0ac509-22db-400e-b1db-202afb599f67
-- title:
--   Simple Graph: card le of edge Inj
-- statement:
--   Un conjunto de dardos con a lo más un dardo por arista tiene a lo más `|E|` elementos.
--
--   Source: https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Orientation.lean#L151-L157
-- source:
--   https://github.com/jtraverso/euler-petersen/blob/02c3f1a5327c5f066938860bb07e9fce226b36ca/Euler/Orientation.lean#L151-L157

module
public import Definitions.Def_Euler_Trail
public import Definitions.Def_Euler_Orientation
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem SimpleGraph.card_le_of_edgeInj {Ds : Finset G.Dart} (hinj : EdgeInj Ds) :
    Ds.card ≤ G.edgeFinset.card := by sorry
