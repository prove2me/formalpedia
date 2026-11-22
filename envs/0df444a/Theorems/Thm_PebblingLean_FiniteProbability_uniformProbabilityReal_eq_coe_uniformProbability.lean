-- Prove2me | Theorems.Thm_PebblingLean_FiniteProbability_uniformProbabilityReal_eq_coe_uniformProbability
-- name    : PebblingLean.FiniteProbability.uniformProbabilityReal_eq_coe_uniformProbability
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:46:43.378034+00:00
-- url     : https://prove2.me/theorems/29145453-dca3-439f-bada-d631f0357a66
-- title:
--   Finite Probability: uniform Probability Real eq coe uniform Probability
-- statement:
--   The Finite Probability construction uses the uniform Probability Real eq coe uniform Probability property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L42-L45
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L42-L45

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

theorem PebblingLean.FiniteProbability.uniformProbabilityReal_eq_coe_uniformProbability [Fintype Ω]
    (P : Ω → Prop) [DecidablePred P] :
    uniformProbabilityReal P = (uniformProbability P : ℝ) := by sorry
