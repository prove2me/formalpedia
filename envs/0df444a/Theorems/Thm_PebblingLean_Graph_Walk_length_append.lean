-- Prove2me | Theorems.Thm_PebblingLean_Graph_Walk_length_append
-- name    : PebblingLean.Graph.Walk.length_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:48.392547+00:00
-- url     : https://prove2.me/theorems/76c9a284-d372-4be7-8c4e-cccf1f96ac7d
-- title:
--   Walk: length append
-- statement:
--   The Walk construction uses the length append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L52-L58
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L52-L58

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_PebblingLean_Delivery
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Graph
variable {V : Type u} (G : Graph V)
open PebblingLean.Graph.Walk

theorem PebblingLean.Graph.Walk.length_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (Graph.Walk.append G p q).length = p.length + q.length := by sorry
