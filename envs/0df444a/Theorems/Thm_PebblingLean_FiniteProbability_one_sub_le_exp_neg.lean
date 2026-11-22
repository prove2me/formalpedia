-- Prove2me | Theorems.Thm_PebblingLean_FiniteProbability_one_sub_le_exp_neg
-- name    : PebblingLean.FiniteProbability.one_sub_le_exp_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:27.255814+00:00
-- url     : https://prove2.me/theorems/18b5cf00-034e-4f3c-a6cd-3baa799724ce
-- title:
--   Finite Probability: one sub le exp neg
-- statement:
--   The Finite Probability construction uses the one sub le exp neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L173-L176
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L173-L176

module
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Definitions.Def_LeanPool_PebblingLean_FiniteProbability
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_Concentration
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.FiniteProbability
variable {Ω : Type*}

theorem PebblingLean.FiniteProbability.one_sub_le_exp_neg (u : ℝ) :
    1 - u ≤ Real.exp (-u) := by sorry
