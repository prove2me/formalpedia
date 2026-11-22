-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_dist_adj_le_succ
-- name    : PebblingLean.Hypercube.dist_adj_le_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:16.612936+00:00
-- url     : https://prove2.me/theorems/78604a9e-3e42-4056-bb2f-61a4e27a8657
-- title:
--   Hypercube: dist adj le succ
-- statement:
--   Adjacent hypercube vertices have distances to any third vertex that differ
--   by at most one in this direction.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Hypercube.lean#L155-L159
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Hypercube.lean#L155-L159

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube

theorem PebblingLean.Hypercube.dist_adj_le_succ {n : ℕ} {x y t : HypercubeVertex n}
    (hxy : (graph n).Adj x y) : dist x t ≤ dist y t + 1 := by sorry
