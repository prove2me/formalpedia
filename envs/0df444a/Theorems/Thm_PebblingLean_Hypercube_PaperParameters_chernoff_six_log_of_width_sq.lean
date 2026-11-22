-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_chernoff_six_log_of_width_sq
-- name    : PebblingLean.Hypercube.PaperParameters.chernoff_six_log_of_width_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:02:25.936875+00:00
-- url     : https://prove2.me/theorems/129a0f2d-efb1-4858-8c63-b433a38fc92b
-- title:
--   Paper Parameters: chernoff six log of width sq
-- statement:
--   Algebraic form of the Chernoff exponent target with `E_n=6 log n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3636-L3651
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3636-L3651

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

theorem PebblingLean.Hypercube.PaperParameters.chernoff_six_log_of_width_sq {A K : ℝ} {n : ℕ}
    (hwidthSq :
      12 * ((splitA K n : ℝ) + 1) * Real.log (n : ℝ) ≤
        (annulusWidth A K n : ℝ) ^ 2) :
    6 * Real.log (n : ℝ) ≤
      (1 / 2) *
        ((annulusWidth A K n : ℝ) ^ 2 /
          ((splitA K n : ℝ) + 1)) := by sorry
