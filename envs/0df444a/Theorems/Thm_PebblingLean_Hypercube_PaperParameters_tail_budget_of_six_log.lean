-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_tail_budget_of_six_log
-- name    : PebblingLean.Hypercube.PaperParameters.tail_budget_of_six_log
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:57:07.542465+00:00
-- url     : https://prove2.me/theorems/f423e321-746e-4339-8057-46217fed57c2
-- title:
--   Paper Parameters: tail budget of six log
-- statement:
--   A convenient way to discharge the tail budget: for `n≥2`,
--   `log 16 + 2 log n ≤ 6 log n`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2083-L2097
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L2083-L2097

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

theorem PebblingLean.Hypercube.PaperParameters.tail_budget_of_six_log {n : ℕ} {E : ℝ}
    (hn : 2 ≤ n)
    (hE : 6 * Real.log (n : ℝ) ≤ E) :
    Real.log 16 + 2 * Real.log (n : ℝ) ≤ E := by sorry
