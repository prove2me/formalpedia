-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_minOccupiedPileSize_stackListDistribution
-- name    : PebblingLean.Hypercube.minOccupiedPileSize_stackListDistribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:51:35.227893+00:00
-- url     : https://prove2.me/theorems/21e20436-2cfa-4fa9-9bcf-fcaaf2d09274
-- title:
--   Hypercube: min Occupied Pile Size stack List Distribution
-- statement:
--   Every occupied pile in a stack-list distribution has at least one full
--   stack.  Repeated centers only increase the pile size.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundDelivery.lean#L61-L77
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundDelivery.lean#L61-L77

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

theorem PebblingLean.Hypercube.minOccupiedPileSize_stackListDistribution {n rOut : ℕ}
    (centers : List (HypercubeVertex n)) :
    MinOccupiedPileSize (stackListDistribution (n := n) rOut centers) (2 ^ rOut) := by sorry
