-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_Paper_one_le_CLean_sum
-- name    : PebblingLean.Hypercube.Paper.one_le_CLean_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:03:56.04083+00:00
-- url     : https://prove2.me/theorems/b94aa2f2-8b4b-4224-bf43-6c53ce1d7c73
-- title:
--   Paper: one le CLean sum
-- statement:
--   The Paper construction uses the one le CLean sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L90-L105
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L90-L105

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

theorem PebblingLean.Hypercube.Paper.one_le_CLean_sum :
    (1 : ℝ) ≤
      ∑ j ∈ Finset.range N0,
        (2 ^ (j / 5) : ℝ) * (((3 : ℝ) / 2) ^ j) := by sorry
