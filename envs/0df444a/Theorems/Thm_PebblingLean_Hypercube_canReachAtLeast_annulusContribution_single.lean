-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_canReachAtLeast_annulusContribution_single
-- name    : PebblingLean.Hypercube.canReachAtLeast_annulusContribution_single
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:51:36.995864+00:00
-- url     : https://prove2.me/theorems/2f23c2ac-b96a-4557-97a2-cbdac8b283da
-- title:
--   Hypercube: can Reach At Least annulus Contribution single
-- statement:
--   A stack of size `2^rOut` at an annulus center can directly deliver the
--   annulus contribution assigned to that center.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundDelivery.lean#L81-L99
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundDelivery.lean#L81-L99

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBound
public import Definitions.Def_LeanPool_PebblingLean_Delivery
public import Definitions.Def_LeanPool_PebblingLean_HypercubePath
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling

theorem PebblingLean.Hypercube.canReachAtLeast_annulusContribution_single {n rIn rOut : ℕ}
    {target center : HypercubeVertex n}
    (hmem : center ∈ annulus n rIn rOut target) :
    CanReachAtLeast (graph n)
      (Pebbling.single center (2 ^ rOut)) target
      (annulusContribution rIn rOut target center) := by sorry
