-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_nat_mul_log_mono_from_one
-- name    : PebblingLean.Hypercube.PaperParameters.nat_mul_log_mono_from_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:57:05.582993+00:00
-- url     : https://prove2.me/theorems/4fe545a7-3875-4a08-bbde-173f8681fb52
-- title:
--   Paper Parameters: nat mul log mono from one
-- statement:
--   Monotonicity of the integer sequence `n log n` for `n≥1`, in the only
--   form needed for cutoff propagation.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1563-L1576
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L1563-L1576

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

theorem PebblingLean.Hypercube.PaperParameters.nat_mul_log_mono_from_one {n0 n : ℕ}
    (hn0_pos : 1 ≤ n0)
    (hn : n0 ≤ n) :
    (n0 : ℝ) * Real.log (n0 : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) := by sorry
