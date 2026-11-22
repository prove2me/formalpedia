-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_binomialWindowProbThird_lower_of_tails_le
-- name    : PebblingLean.Hypercube.binomialWindowProbThird_lower_of_tails_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:12.903628+00:00
-- url     : https://prove2.me/theorems/e72814cb-47e8-4b7d-90bc-4ce568d9a5c6
-- title:
--   Hypercube: binomial Window Prob Third lower of tails le
-- statement:
--   If the two binomial tails outside the annulus have total mass at most
--   `eps`, then the annulus window has mass at least `1-eps`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L532-L539
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L532-L539

module
public import Definitions.Def_LeanPool_PebblingLean_Concentration
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundDelivery
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundProbability
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open Pebbling
open FiniteProbability

theorem PebblingLean.Hypercube.binomialWindowProbThird_lower_of_tails_le
    {n rIn rOut : ℕ} {eps : ℝ} (hr : rIn ≤ rOut)
    (htails :
      binomialLeftTailProbThird n rIn +
          binomialRightTailProbThird n rOut ≤ eps) :
    1 - eps ≤ binomialWindowProbThird n rIn rOut := by sorry
