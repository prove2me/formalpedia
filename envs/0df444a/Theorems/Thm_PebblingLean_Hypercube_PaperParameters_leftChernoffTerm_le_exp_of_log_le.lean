-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_leftChernoffTerm_le_exp_of_log_le
-- name    : PebblingLean.Hypercube.PaperParameters.leftChernoffTerm_le_exp_of_log_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:57:20.075969+00:00
-- url     : https://prove2.me/theorems/ff449d1a-138a-484d-b8da-c1ef7e9d1ec9
-- title:
--   Paper Parameters: left Chernoff Term le exp of log le
-- statement:
--   Logarithmic form of the left Chernoff term.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3364-L3390
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3364-L3390

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters

theorem PebblingLean.Hypercube.PaperParameters.leftChernoffTerm_le_exp_of_log_le {A K : ℝ} {lam : ℕ → ℝ}
    {n : ℕ} {E : ℝ}
    (hlog :
      lam n * (rIn A K n : ℝ) +
          (splitA K n : ℝ) *
            Real.log (((1 : ℝ) / 3) * Real.exp (-(lam n)) +
              ((2 : ℝ) / 3)) ≤ -E) :
    leftChernoffTerm A K lam n ≤ Real.exp (-E) := by sorry
