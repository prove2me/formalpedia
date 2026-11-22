-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_cost_uniform_bound_of_geometric_loss
-- name    : PebblingLean.Hypercube.LossRecurrence.cost_uniform_bound_of_geometric_loss
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:57:35.630428+00:00
-- url     : https://prove2.me/theorems/377d5ea2-4e0f-43c6-a984-b87e0745bd8d
-- title:
--   Loss Recurrence: cost uniform bound of geometric loss
-- statement:
--   Uniform normalized-cost bound when the loss sequence decays geometrically
--   along recursive paths.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L275-L303
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L275-L303

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

theorem PebblingLean.Hypercube.LossRecurrence.cost_uniform_bound_of_geometric_loss
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 : ℕ} {B q M G : ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hM : 0 ≤ M)
    (hq_nonneg : 0 ≤ q)
    (hnext : ∀ n : ℕ, n0 ≤ n → next n < n)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hbase : ∀ n : ℕ, n < n0 → R n ≤ B)
    (hdecay :
      ∀ n : ℕ, n0 ≤ n → n0 ≤ next n → loss n ≤ q * loss (next n))
    (hbound : ∀ n : ℕ, n0 ≤ n → loss n ≤ M)
    (hgeom : ∀ k : ℕ, geomSum q k ≤ G) (n : ℕ) :
    R n ≤ Real.exp (G * M) * B := by sorry
