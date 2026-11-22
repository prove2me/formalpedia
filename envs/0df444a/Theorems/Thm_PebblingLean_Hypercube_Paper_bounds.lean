-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_Paper_bounds
-- name    : PebblingLean.Hypercube.Paper.bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:47.869425+00:00
-- url     : https://prove2.me/theorems/fbf78728-d02d-4202-9ea5-3299d65ebf21
-- title:
--   Paper: bounds
-- statement:
--   The two inequalities in the final theorem, stated directly for
--   `optimalPebblingNumber`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L169-L173
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L169-L173

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

theorem PebblingLean.Hypercube.Paper.bounds (n : ℕ) :
    ((4 : ℝ) / 3) ^ n ≤ (optimalPebblingNumber n : ℝ) ∧
      (optimalPebblingNumber n : ℝ) ≤
        CLean * (((4 : ℝ) / 3) ^ n) := by sorry
