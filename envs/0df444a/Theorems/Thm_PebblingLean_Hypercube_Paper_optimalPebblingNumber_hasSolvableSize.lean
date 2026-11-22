-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_Paper_optimalPebblingNumber_hasSolvableSize
-- name    : PebblingLean.Hypercube.Paper.optimalPebblingNumber_hasSolvableSize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:04:04.506664+00:00
-- url     : https://prove2.me/theorems/c7755806-6a22-4a9e-a5a3-bae91c7179fb
-- title:
--   Paper: optimal Pebbling Number has Solvable Size
-- statement:
--   The Paper construction uses the optimal Pebbling Number has Solvable Size property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L129-L133
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L129-L133

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

theorem PebblingLean.Hypercube.Paper.optimalPebblingNumber_hasSolvableSize (n : ℕ) :
    HasSolvableSize (graph n) (optimalPebblingNumber n) := by sorry
