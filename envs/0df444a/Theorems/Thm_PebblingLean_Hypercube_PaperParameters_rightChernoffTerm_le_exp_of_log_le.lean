-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_rightChernoffTerm_le_exp_of_log_le
-- name    : PebblingLean.Hypercube.PaperParameters.rightChernoffTerm_le_exp_of_log_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:57:20.118414+00:00
-- url     : https://prove2.me/theorems/5c5cd129-4c88-4426-8cf4-d11fe2891913
-- title:
--   Paper Parameters: right Chernoff Term le exp of log le
-- statement:
--   Logarithmic form of the right Chernoff term.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3393-L3419
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3393-L3419

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

theorem PebblingLean.Hypercube.PaperParameters.rightChernoffTerm_le_exp_of_log_le {A K : ℝ} {lam : ℕ → ℝ}
    {n : ℕ} {E : ℝ}
    (hlog :
      -(lam n * (rOut A K n : ℝ)) +
          (splitA K n : ℝ) *
            Real.log (((1 : ℝ) / 3) * Real.exp (lam n) +
              ((2 : ℝ) / 3)) ≤ -E) :
    rightChernoffTerm A K lam n ≤ Real.exp (-E) := by sorry
