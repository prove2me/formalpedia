-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_annulusWeightedTerm_eq_fullFactor_mul_binomialTerm
-- name    : PebblingLean.Hypercube.annulusWeightedTerm_eq_fullFactor_mul_binomialTerm
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:51:54.366386+00:00
-- url     : https://prove2.me/theorems/ec392104-fd5b-45cf-a73a-95c5f025c745
-- title:
--   Hypercube: annulus Weighted Term eq full Factor mul binomial Term
-- statement:
--   Termwise conversion between the annulus contribution weight and the
--   `Binomial(1/3)` mass after factoring out the full weighted mean
--   `2^rOut (3/4)^n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L366-L394
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundProbability.lean#L366-L394

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

theorem PebblingLean.Hypercube.annulusWeightedTerm_eq_fullFactor_mul_binomialTerm
    {n rOut i : ℕ} (hin : i ≤ n) (hr : i ≤ rOut) :
    (2 ^ (rOut - i) : ℝ) / (2 ^ n : ℝ) =
      (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) *
        ((((1 : ℝ) / 3) ^ i) * (((2 : ℝ) / 3) ^ (n - i))) := by sorry
