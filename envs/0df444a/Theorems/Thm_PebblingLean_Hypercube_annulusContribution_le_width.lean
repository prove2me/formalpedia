-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_annulusContribution_le_width
-- name    : PebblingLean.Hypercube.annulusContribution_le_width
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:32.093287+00:00
-- url     : https://prove2.me/theorems/b084dcf6-9e49-42e4-93cb-1473a46a3502
-- title:
--   Hypercube: annulus Contribution le width
-- statement:
--   If the center is counted, the annulus contribution is bounded by the width
--   of the annulus rather than by the full stack size.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBound.lean#L74-L82
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBound.lean#L74-L82

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

theorem PebblingLean.Hypercube.annulusContribution_le_width {n rIn rOut : ℕ}
    (target center : HypercubeVertex n) :
    annulusContribution rIn rOut target center ≤ 2 ^ (rOut - rIn) := by sorry
