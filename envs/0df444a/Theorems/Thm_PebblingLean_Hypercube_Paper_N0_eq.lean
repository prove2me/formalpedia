-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_Paper_N0_eq
-- name    : PebblingLean.Hypercube.Paper.N0_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:13:36.364496+00:00
-- url     : https://prove2.me/theorems/1dd9c014-046c-4d0f-96b4-243b42b2e8a6
-- title:
--   Paper: N0 eq
-- statement:
--   The Paper construction uses the N0 eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L38-L40
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Paper.lean#L38-L40

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

theorem PebblingLean.Hypercube.Paper.N0_eq :
    N0 = 36_329_454_321_664 := by sorry
