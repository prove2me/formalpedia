-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_annulusContribution_le_stackSize
-- name    : PebblingLean.Hypercube.annulusContribution_le_stackSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:52:59.4378+00:00
-- url     : https://prove2.me/theorems/04ca6651-4e56-4bdf-b269-24c5b8f2e280
-- title:
--   Hypercube: annulus Contribution le stack Size
-- statement:
--   One annulus contribution is bounded by the stack size `2^rOut`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBound.lean#L63-L70
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBound.lean#L63-L70

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

theorem PebblingLean.Hypercube.annulusContribution_le_stackSize {n rIn rOut : ℕ}
    (target center : HypercubeVertex n) :
    annulusContribution rIn rOut target center ≤ 2 ^ rOut := by sorry
