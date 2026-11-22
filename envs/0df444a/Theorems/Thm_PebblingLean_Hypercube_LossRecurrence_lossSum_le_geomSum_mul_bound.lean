-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_lossSum_le_geomSum_mul_bound
-- name    : PebblingLean.Hypercube.LossRecurrence.lossSum_le_geomSum_mul_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:57:32.941796+00:00
-- url     : https://prove2.me/theorems/6b9afa62-9586-42b5-836f-a9399181eea9
-- title:
--   Loss Recurrence: loss Sum le geom Sum mul bound
-- statement:
--   Geometric domination of a finite loss sum along an active recursive path.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L241-L271
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L241-L271

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.LossRecurrence

theorem PebblingLean.Hypercube.LossRecurrence.lossSum_le_geomSum_mul_bound
    {next : ℕ → ℕ} {loss : ℕ → ℝ} {n0 : ℕ} {q M : ℝ}
    (hq_nonneg : 0 ≤ q)
    (hdecay :
      ∀ n : ℕ, n0 ≤ n → n0 ≤ next n → loss n ≤ q * loss (next n))
    (hbound : ∀ n : ℕ, n0 ≤ n → loss n ≤ M)
    (k n : ℕ) (hactive : ActiveFor next n0 k n) :
    lossSum next loss k n ≤ geomSum q k * M := by sorry
