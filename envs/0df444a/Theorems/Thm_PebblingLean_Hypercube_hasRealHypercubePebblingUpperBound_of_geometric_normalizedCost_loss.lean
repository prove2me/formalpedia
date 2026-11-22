-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_hasRealHypercubePebblingUpperBound_of_geometric_normalizedCost_loss
-- name    : PebblingLean.Hypercube.hasRealHypercubePebblingUpperBound_of_geometric_normalizedCost_loss
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-22T05:54:57.76705+00:00
-- url     : https://prove2.me/theorems/b9ceb3ab-bc7b-482c-9610-3d93ee8e5d33
-- title:
--   Hypercube: has Real Hypercube Pebbling Upper Bound of geometric normalized Cost loss
-- statement:
--   Final abstract bridge from the geometric normalized-cost recurrence to the
--   real asymptotic upper-bound statement.  After the numerical parameter choices
--   prove the hypotheses here, this is the formal end of the upper-bound proof.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L434-L461
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundLoss.lean#L434-L461

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

theorem PebblingLean.Hypercube.hasRealHypercubePebblingUpperBound_of_geometric_normalizedCost_loss
    {costBound next : ℕ → ℕ} {loss : ℕ → ℝ} {n0 : ℕ}
    {B q M : ℝ}
    (hupper : HasHypercubePebblingUpperBound costBound)
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hM : 0 ≤ M)
    (hq_nonneg : 0 ≤ q)
    (hq_half : q ≤ (1 : ℝ) / 2)
    (hnext : ∀ n : ℕ, n0 ≤ n → next n < n)
    (hstep :
      ∀ n : ℕ, n0 ≤ n →
        normalizedCost costBound n ≤
          (1 + loss n) * normalizedCost costBound (next n))
    (hbase :
      ∀ n : ℕ, n < n0 → normalizedCost costBound n ≤ B)
    (hdecay :
      ∀ n : ℕ, n0 ≤ n → n0 ≤ next n → loss n ≤ q * loss (next n))
    (hbound : ∀ n : ℕ, n0 ≤ n → loss n ≤ M) :
    HasRealHypercubePebblingUpperBound (Real.exp (2 * M) * B) := by sorry
