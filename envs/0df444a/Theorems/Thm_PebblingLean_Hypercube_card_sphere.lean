-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_card_sphere
-- name    : PebblingLean.Hypercube.card_sphere
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:05.587861+00:00
-- url     : https://prove2.me/theorems/b4154fab-3eaa-4739-8e95-52b1d4382a8f
-- title:
--   Hypercube: card sphere
-- statement:
--   The Hamming sphere of radius `k` around any fixed hypercube vertex has
--   cardinality `n choose k`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Hypercube.lean#L94-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Hypercube.lean#L94-L108

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

theorem PebblingLean.Hypercube.card_sphere {n : ℕ} (base : HypercubeVertex n) (k : ℕ) :
    Fintype.card {v : HypercubeVertex n // dist base v = k} = Nat.choose n k := by sorry
