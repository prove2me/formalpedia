-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_Paper_CLean_eq_paper_formula
-- name    : PebblingLean.Hypercube.Paper.CLean_eq_paper_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:44.129685+00:00
-- url     : https://prove2.me/theorems/693c0301-a1c6-4297-945c-52732f60ed97
-- title:
--   Paper: CLean eq paper formula
-- statement:
--   The same constant in the displayed form used in the paper.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L57-L88
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L57-L88

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

theorem PebblingLean.Hypercube.Paper.CLean_eq_paper_formula :
    CLean =
      Real.exp (4 / (N0 : ℝ) ^ 2) *
        ∑ j ∈ Finset.range N0,
          (2 ^ (j / 5) : ℝ) * (((3 : ℝ) / 2) ^ j) := by sorry
