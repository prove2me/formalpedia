-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_Paper_lower_bound
-- name    : PebblingLean.Hypercube.Paper.lower_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:46.491806+00:00
-- url     : https://prove2.me/theorems/8d55c850-8283-49df-80be-cf05e47546e2
-- title:
--   Paper: lower bound
-- statement:
--   Paper lower bound: `o(Q_n) ≥ (4/3)^n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L145-L148
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L145-L148

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

theorem PebblingLean.Hypercube.Paper.lower_bound (n : ℕ) :
    ((4 : ℚ) / 3) ^ n ≤ (optimalPebblingNumber n : ℚ) := by sorry
