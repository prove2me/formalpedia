-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_Paper_upper_bound
-- name    : PebblingLean.Hypercube.Paper.upper_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:04:01.54939+00:00
-- url     : https://prove2.me/theorems/bb5fa9c2-9e7c-4252-9641-d0c9a0ba0186
-- title:
--   Paper: upper bound
-- statement:
--   Paper upper bound with the explicit Lean constant.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L160-L165
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L160-L165

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

theorem PebblingLean.Hypercube.Paper.upper_bound (n : ℕ) :
    (optimalPebblingNumber n : ℝ) ≤
      CLean * (((4 : ℝ) / 3) ^ n) := by sorry
