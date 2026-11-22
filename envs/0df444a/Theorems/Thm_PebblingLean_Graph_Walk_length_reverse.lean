-- Prove2me | Theorems.Thm_PebblingLean_Graph_Walk_length_reverse
-- name    : PebblingLean.Graph.Walk.length_reverse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:49.120823+00:00
-- url     : https://prove2.me/theorems/d3e7bce9-f1dd-4896-b429-122e7203eeec
-- title:
--   Walk: length reverse
-- statement:
--   The Walk construction uses the length reverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L66-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Delivery.lean#L66-L72

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

theorem PebblingLean.Graph.Walk.length_reverse {u v : V} (p : G.Walk u v) :
    p.reverse.length = p.length := by sorry
