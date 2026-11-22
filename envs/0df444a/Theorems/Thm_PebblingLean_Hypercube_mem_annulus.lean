-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_mem_annulus
-- name    : PebblingLean.Hypercube.mem_annulus
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:14.372187+00:00
-- url     : https://prove2.me/theorems/bf594101-326e-41b9-bcad-6aa4773fa0b6
-- title:
--   Hypercube: mem annulus
-- statement:
--   The Hypercube construction uses the mem annulus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBound.lean#L35-L38
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBound.lean#L35-L38

module
public import Definitions.Def_LeanPool_PebblingLean_Hypercube
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling

theorem PebblingLean.Hypercube.mem_annulus {n rIn rOut : ℕ} {target center : HypercubeVertex n} :
    center ∈ annulus n rIn rOut target ↔
      rIn ≤ dist center target ∧ dist center target ≤ rOut := by sorry
