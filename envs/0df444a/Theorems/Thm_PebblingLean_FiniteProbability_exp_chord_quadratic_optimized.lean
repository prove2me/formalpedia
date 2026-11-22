-- Prove2me | Theorems.Thm_PebblingLean_FiniteProbability_exp_chord_quadratic_optimized
-- name    : PebblingLean.FiniteProbability.exp_chord_quadratic_optimized
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:31.259806+00:00
-- url     : https://prove2.me/theorems/618a601b-93d5-40a5-abc6-55c84f57fe35
-- title:
--   Finite Probability: exp chord quadratic optimized
-- statement:
--   Algebraic optimization for the chord-based bounded-nonnegative Chernoff
--   bound.  If `mu` exceeds the threshold `T` by `gap`, then the choice
--   `λ = gap/(2 B mu)` gives the usual quadratic exponent.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L203-L219
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L203-L219

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

theorem PebblingLean.FiniteProbability.exp_chord_quadratic_optimized {T gap B mu lam : ℝ}
    (hB : 0 < B) (hmu : 0 < mu) (hgap : 0 ≤ gap)
    (hmean : T + gap ≤ mu)
    (hlam : lam = gap / (2 * B * mu)) :
    Real.exp (lam * T - (lam - lam ^ 2 * B) * mu) ≤
      Real.exp (-(gap ^ 2 / (4 * B * mu))) := by sorry
