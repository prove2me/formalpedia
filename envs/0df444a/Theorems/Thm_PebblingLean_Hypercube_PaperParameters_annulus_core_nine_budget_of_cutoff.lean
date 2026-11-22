-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_annulus_core_nine_budget_of_cutoff
-- name    : PebblingLean.Hypercube.PaperParameters.annulus_core_nine_budget_of_cutoff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:00:16.979117+00:00
-- url     : https://prove2.me/theorems/0dc6df36-9b8f-4f30-892e-aa199803e54c
-- title:
--   Paper Parameters: annulus core nine budget of cutoff
-- statement:
--   The coarse `core≥9` square budget propagates from the cutoff because
--   `n log n` is monotone for `n≥1`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1580-L1594
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1580-L1594

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

theorem PebblingLean.Hypercube.PaperParameters.annulus_core_nine_budget_of_cutoff {A : ℝ} {n0 n : ℕ}
    (hn0_pos : 1 ≤ n0) (hn : n0 ≤ n)
    (hcutoff :
      81 ≤ A ^ 2 * (((3 : ℝ) * (n0 : ℝ) / 4) *
        Real.log (n0 : ℝ))) :
    81 ≤ A ^ 2 * (((3 : ℝ) * (n : ℝ) / 4) *
      Real.log (n : ℝ)) := by sorry
