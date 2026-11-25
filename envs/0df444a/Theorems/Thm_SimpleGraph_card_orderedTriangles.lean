-- Prove2me | Theorems.Thm_SimpleGraph_card_orderedTriangles
-- name    : SimpleGraph.card_orderedTriangles
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:30:47.510209+00:00
-- url     : https://prove2.me/theorems/8abeebea-64cc-4c3a-aad5-583ea636d3e6
-- title:
--   Simple Graph: card ordered Triangles
-- statement:
--   Each triangle gives six ordered triangles.
--
--   Source: https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L184-L210
-- source:
--   https://github.com/Egly443/lean-ramsey-reservoir/blob/7024820542e42feb8177cbf2c624d64106813332/RamseyReservoir/Book.lean#L184-L210

module
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Definitions.Def_RamseyReservoir_Book
set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V] [DecidableRel G.Adj]

theorem SimpleGraph.card_orderedTriangles [DecidableEq V] :
    #G.orderedTriangles = 6 * #(G.cliqueFinset 3) := by sorry
