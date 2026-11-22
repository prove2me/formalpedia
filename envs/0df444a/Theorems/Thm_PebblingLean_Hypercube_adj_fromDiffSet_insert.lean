-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_adj_fromDiffSet_insert
-- name    : PebblingLean.Hypercube.adj_fromDiffSet_insert
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:51:25.862727+00:00
-- url     : https://prove2.me/theorems/61821d50-9c17-4366-8c7b-9f5042ffecf6
-- title:
--   Hypercube: adj from Diff Set insert
-- statement:
--   Flipping one new coordinate gives an adjacent hypercube vertex.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubePath.lean#L52-L55
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubePath.lean#L52-L55

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Definitions.Def_LeanPool_PebblingLean_Delivery
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_PebblingLean_HypercubePath
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling

theorem PebblingLean.Hypercube.adj_fromDiffSet_insert {n : ℕ} (base : HypercubeVertex n)
    {s : Finset (Fin n)} {i : Fin n} (hi : i ∉ s) :
    (graph n).Adj (fromDiffSet base s) (fromDiffSet base (insert i s)) := by sorry
