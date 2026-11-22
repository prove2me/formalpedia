-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_binomialWindowProbThird_add_tails_eq_one
-- name    : PebblingLean.Hypercube.binomialWindowProbThird_add_tails_eq_one
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:52:07.847846+00:00
-- url     : https://prove2.me/theorems/e8b3d4cd-4f30-44a9-866a-7b8b85bacefb
-- title:
--   Hypercube: binomial Window Prob Third add tails eq one
-- statement:
--   Window probability plus the two outside tails equals one.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L514-L528
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L514-L528

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

theorem PebblingLean.Hypercube.binomialWindowProbThird_add_tails_eq_one
    (n rIn rOut : ℕ) (hr : rIn ≤ rOut) :
    binomialWindowProbThird n rIn rOut +
        binomialLeftTailProbThird n rIn +
          binomialRightTailProbThird n rOut = 1 := by sorry
