-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_exists_walk_length_dist
-- name    : PebblingLean.Hypercube.exists_walk_length_dist
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:31.445706+00:00
-- url     : https://prove2.me/theorems/9b6f6a6e-5776-42c5-85c5-6487bb5c1fff
-- title:
--   Hypercube: exists walk length dist
-- statement:
--   Hypercube Hamming distance is realized by a graph walk of the same length.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubePath.lean#L72-L79
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/HypercubePath.lean#L72-L79

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

theorem PebblingLean.Hypercube.exists_walk_length_dist {n : ℕ} (x y : HypercubeVertex n) :
    ∃ walk : (graph n).Walk x y, walk.length = dist x y := by sorry
