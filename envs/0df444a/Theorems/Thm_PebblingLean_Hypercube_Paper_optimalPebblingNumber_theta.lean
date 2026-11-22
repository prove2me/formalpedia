-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_Paper_optimalPebblingNumber_theta
-- name    : PebblingLean.Hypercube.Paper.optimalPebblingNumber_theta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:14:17.512809+00:00
-- url     : https://prove2.me/theorems/09f7e5d8-be57-4ab0-b338-61a0ad17e3ec
-- title:
--   Paper: optimal Pebbling Number theta
-- statement:
--   Paper conclusion: the optimal pebbling number of the hypercube has order
--   `(4/3)^n`.  This is stated as an explicit two-sided big-Theta witness.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L177-L183
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L177-L183

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Paper
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.Paper
open Pebbling

theorem PebblingLean.Hypercube.Paper.optimalPebblingNumber_theta :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ,
        ((4 : ℝ) / 3) ^ n ≤ (optimalPebblingNumber n : ℝ) ∧
          (optimalPebblingNumber n : ℝ) ≤
            C * (((4 : ℝ) / 3) ^ n) := by sorry
