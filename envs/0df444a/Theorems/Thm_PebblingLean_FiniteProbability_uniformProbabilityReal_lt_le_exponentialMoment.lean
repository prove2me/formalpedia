-- Prove2me | Theorems.Thm_PebblingLean_FiniteProbability_uniformProbabilityReal_lt_le_exponentialMoment
-- name    : PebblingLean.FiniteProbability.uniformProbabilityReal_lt_le_exponentialMoment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:11.540821+00:00
-- url     : https://prove2.me/theorems/0992c455-3bd1-4df2-84c7-763ddeb0ac79
-- title:
--   Finite Probability: uniform Probability Real lt le exponential Moment
-- statement:
--   Chernoff's exponential-moment step for a lower tail, proved here as
--   Markov's inequality applied to `exp(λ(T - X))`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L90-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L90-L108

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

theorem PebblingLean.FiniteProbability.uniformProbabilityReal_lt_le_exponentialMoment [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) {T lam : ℝ} (hlam : 0 < lam) :
    uniformProbabilityReal (fun ω : Ω => X ω < T) ≤
      uniformExpectationReal fun ω : Ω => Real.exp (lam * (T - X ω)) := by sorry
