-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_margin_of_sqrt_margin
-- name    : PebblingLean.Hypercube.PaperParameters.stack_margin_of_sqrt_margin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:59:53.862813+00:00
-- url     : https://prove2.me/theorems/e33f383c-6148-4b52-a58b-2612773b96c4
-- title:
--   Paper Parameters: stack margin of sqrt margin
-- statement:
--   Coefficient form of the corrected stack-margin estimate.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1280-L1296
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1280-L1296

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

theorem PebblingLean.Hypercube.PaperParameters.stack_margin_of_sqrt_margin {A K : ℝ} {n : ℕ}
    (hmargin :
      2 * Real.log (n : ℝ) + 3 * Real.log 2 ≤
        ((K / 5 - A * Real.sqrt 3) * Real.log 2) *
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) +
          ((3 : ℝ) * (n : ℝ) / 4) *
            (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3)) :
    Real.log 2 + 2 * Real.log (n : ℝ) +
        (A * Real.sqrt (3 * (n : ℝ) * Real.log (n : ℝ)) + 1) *
          Real.log 2 ≤
      (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) / 5 - 1) *
          Real.log 2 +
        ((3 : ℝ) * (n : ℝ) / 4) *
          (Real.log ((4 : ℝ) / 3) - Real.log 2 / 3) := by sorry
