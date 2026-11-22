-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_size_stackListDistribution
-- name    : PebblingLean.Hypercube.size_stackListDistribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:50:44.368942+00:00
-- url     : https://prove2.me/theorems/97d53bfe-556c-4d95-8cff-a10ca683bec3
-- title:
--   Hypercube: size stack List Distribution
-- statement:
--   The Hypercube construction uses the size stack List Distribution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundDelivery.lean#L48-L57
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundDelivery.lean#L48-L57

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

theorem PebblingLean.Hypercube.size_stackListDistribution {n rOut : ℕ}
    (centers : List (HypercubeVertex n)) :
    size (stackListDistribution rOut centers) = centers.length * 2 ^ rOut := by sorry
