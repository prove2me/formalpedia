-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasSolvableAtMostSize_of_goodCenterList
-- name    : PebblingLean.Hypercube.hasSolvableAtMostSize_of_goodCenterList
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:50:42.104877+00:00
-- url     : https://prove2.me/theorems/daf27eeb-eca3-4ece-9348-2e314855c397
-- title:
--   Hypercube: has Solvable At Most Size of good Center List
-- statement:
--   Costed form of the deterministic interface for the high-demand lemma.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundDelivery.lean#L135-L141
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundDelivery.lean#L135-L141

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

theorem PebblingLean.Hypercube.hasSolvableAtMostSize_of_goodCenterList {n rIn rOut T : ℕ}
    {centers : List (HypercubeVertex n)}
    (hgood : IsGoodCenterList n rIn rOut T centers) :
    HasSolvableAtMostSize (graph n) T (centers.length * 2 ^ rOut) := by sorry
