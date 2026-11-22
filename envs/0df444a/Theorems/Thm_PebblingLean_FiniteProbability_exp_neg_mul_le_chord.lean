-- Prove2me | Theorems.Thm_PebblingLean_FiniteProbability_exp_neg_mul_le_chord
-- name    : PebblingLean.FiniteProbability.exp_neg_mul_le_chord
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:48:18.808401+00:00
-- url     : https://prove2.me/theorems/e70b883d-73c2-40e7-b311-9120dfa6efec
-- title:
--   Finite Probability: exp neg mul le chord
-- statement:
--   Convexity of the exponential gives the chord bound used for bounded
--   nonnegative summands: on `0 ≤ z ≤ B`, `exp(-λ z)` is below the chord joining
--   `0` and `B`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L128-L155
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/Concentration.lean#L128-L155

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

theorem PebblingLean.FiniteProbability.exp_neg_mul_le_chord {lam B z : ℝ}
    (hB : 0 < B) (hz0 : 0 ≤ z) (hzB : z ≤ B) :
    Real.exp (-(lam * z)) ≤
      1 - (1 - Real.exp (-(lam * B))) * (z / B) := by sorry
