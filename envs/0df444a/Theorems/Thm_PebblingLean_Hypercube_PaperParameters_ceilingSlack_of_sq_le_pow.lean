-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_ceilingSlack_of_sq_le_pow
-- name    : PebblingLean.Hypercube.PaperParameters.ceilingSlack_of_sq_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:10.602901+00:00
-- url     : https://prove2.me/theorems/ec835aef-4106-4450-beca-6ae3d21648e3
-- title:
--   Paper Parameters: ceiling Slack of sq le pow
-- statement:
--   Transparent sufficient condition for the ceiling slack: since
--   `loss n = n^{-2}`, it is enough that `(4/3)^a` dominate `n^2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1999-L2009
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1999-L2009

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

theorem PebblingLean.Hypercube.PaperParameters.ceilingSlack_of_sq_le_pow {K : ℝ} {n : ℕ}
    (hn : 0 < n)
    (hpow : (n : ℝ) ^ 2 ≤ (((4 : ℝ) / 3) ^ splitA K n)) :
    1 ≤ loss n * (((4 : ℝ) / 3) ^ splitA K n) := by sorry
