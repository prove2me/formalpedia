-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_width_const_budget_of_cutoff
-- name    : PebblingLean.Hypercube.PaperParameters.width_const_budget_of_cutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:00:17.80894+00:00
-- url     : https://prove2.me/theorems/5dd951a3-5210-4803-83b6-ab0a9ca7e70b
-- title:
--   Paper Parameters: width const budget of cutoff
-- statement:
--   A width constant budget checked at the cutoff propagates to all larger
--   dimensions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1598-L1620
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1598-L1620

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

theorem PebblingLean.Hypercube.PaperParameters.width_const_budget_of_cutoff {K : ℝ} {n0 n : ℕ}
    (hK : 0 ≤ K)
    (hn0_pos : 1 ≤ n0)
    (hn : n0 ≤ n)
    (hcutoff :
      Real.log 128 + 4 * Real.log 2 ≤
        (K / 30 * Real.log 2) *
          Real.sqrt ((n0 : ℝ) * Real.log (n0 : ℝ))) :
    Real.log 128 + 4 * Real.log 2 ≤
      (K / 30 * Real.log 2) *
        Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by sorry
