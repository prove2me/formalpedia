-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_annulusContribution_sq_le_width_mul
-- name    : PebblingLean.Hypercube.annulusContribution_sq_le_width_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:34.243384+00:00
-- url     : https://prove2.me/theorems/e2e0fe31-4125-409f-8d5f-5244ab33931e
-- title:
--   Hypercube: annulus Contribution sq le width mul
-- statement:
--   The square bound used in the Bernstein step: `Z^2 ≤ B_0 Z`, where
--   `B_0 = 2^(rOut-rIn)` is the annulus-width contribution bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBound.lean#L86-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBound.lean#L86-L99

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

theorem PebblingLean.Hypercube.annulusContribution_sq_le_width_mul {n rIn rOut : ℕ}
    (target center : HypercubeVertex n) :
    annulusContribution rIn rOut target center ^ 2 ≤
      2 ^ (rOut - rIn) * annulusContribution rIn rOut target center := by sorry
