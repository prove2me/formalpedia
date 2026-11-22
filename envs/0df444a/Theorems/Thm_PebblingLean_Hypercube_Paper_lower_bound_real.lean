-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_Paper_lower_bound_real
-- name    : PebblingLean.Hypercube.Paper.lower_bound_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:52.206247+00:00
-- url     : https://prove2.me/theorems/73e11ec8-c366-47a9-81ee-7f92a524619c
-- title:
--   Paper: lower bound real
-- statement:
--   Real-valued form of the paper lower bound.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L151-L157
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L151-L157

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

theorem PebblingLean.Hypercube.Paper.lower_bound_real (n : ℕ) :
    ((4 : ℝ) / 3) ^ n ≤ (optimalPebblingNumber n : ℝ) := by sorry
