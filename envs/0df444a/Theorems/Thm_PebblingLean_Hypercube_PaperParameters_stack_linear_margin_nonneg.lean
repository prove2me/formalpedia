-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_stack_linear_margin_nonneg
-- name    : PebblingLean.Hypercube.PaperParameters.stack_linear_margin_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:56:12.268351+00:00
-- url     : https://prove2.me/theorems/8a6e1481-c0e1-4844-b406-dd16eae7d7ca
-- title:
--   Paper Parameters: stack linear margin nonneg
-- statement:
--   The positive linear margin available in the stack estimate:
--   `log(4/3) - (log 2)/3 = (1/3)log(32/27) > 0`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1169-L1182
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1169-L1182

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

theorem PebblingLean.Hypercube.PaperParameters.stack_linear_margin_nonneg :
    0 ≤ Real.log ((4 : ℝ) / 3) - Real.log 2 / 3 := by sorry
