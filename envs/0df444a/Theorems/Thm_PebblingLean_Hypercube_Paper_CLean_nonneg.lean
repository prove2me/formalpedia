-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_Paper_CLean_nonneg
-- name    : PebblingLean.Hypercube.Paper.CLean_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:14:02.677076+00:00
-- url     : https://prove2.me/theorems/962864ae-204d-4859-8705-15acaf6a8524
-- title:
--   Paper: CLean nonneg
-- statement:
--   The Paper construction uses the CLean nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L51-L54
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L51-L54

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

theorem PebblingLean.Hypercube.Paper.CLean_nonneg : 0 ≤ CLean := by sorry
