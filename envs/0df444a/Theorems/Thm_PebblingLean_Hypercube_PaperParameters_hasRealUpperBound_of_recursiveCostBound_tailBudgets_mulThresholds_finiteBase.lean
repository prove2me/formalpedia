-- Prove2me | Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_of_recursiveCostBound_tailBudgets_mulThresholds_finiteBase
-- name    : PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_tailBudgets_mulThresholds_finiteBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T06:01:55.838709+00:00
-- url     : https://prove2.me/theorems/96a87f13-0d9e-4d81-9ed5-abbf7e380536
-- title:
--   Paper Parameters: has Real Upper Bound of recursive Cost Bound tail Budgets mul Thresholds finite Base
-- statement:
--   Current reduced wrapper with all three deterministic threshold hypotheses
--   in multiplication/growth form:
--
--   * the Chernoff tails each have budget `loss/16`;
--   * the Bernstein width threshold has no division;
--   * the stack threshold is `2 n^2 2^rOut ≤ minPile(m)(4/3)^a`;
--   * ceiling slack is `(4/3)^a ≥ n^2`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3305-L3349
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/PebblingLean/UpperBoundParameters.lean#L3305-L3349

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

theorem PebblingLean.Hypercube.PaperParameters.hasRealUpperBound_of_recursiveCostBound_tailBudgets_mulThresholds_finiteBase
    {K A : ℝ} {n0 : ℕ} {lamLeft lamRight : ℕ → ℝ}
    (hn0_pos : 0 < n0)
    (hquarter :
      ∀ n : ℕ, n0 ≤ n → 4 * splitM K n ≤ n)
    (hlamLeft :
      ∀ n : ℕ, n0 ≤ n → 0 ≤ lamLeft n)
    (hlamRight :
      ∀ n : ℕ, n0 ≤ n → 0 ≤ lamRight n)
    (hleft :
      ∀ n : ℕ, n0 ≤ n →
        Real.exp (lamLeft n * (rIn A K n : ℝ)) *
            (((1 : ℝ) / 3) * Real.exp (-(lamLeft n)) + ((2 : ℝ) / 3)) ^
              splitA K n ≤
        loss n / 16)
    (hright :
      ∀ n : ℕ, n0 ≤ n →
        Real.exp (-(lamRight n * (rOut A K n : ℝ))) *
            (((1 : ℝ) / 3) * Real.exp (lamRight n) + ((2 : ℝ) / 3)) ^
              splitA K n ≤
        loss n / 16)
    (hlogWidthMul :
      ∀ n : ℕ, n0 ≤ n →
        128 * (2 ^ (2 * annulusWidth A K n) : ℝ) *
            (((splitA K n + 1 : ℕ) : ℝ) * Real.log 2) ≤
          (loss n) ^ 2 * (minPile (splitM K n) : ℝ))
    (hstackMul :
      ∀ n : ℕ, n0 ≤ n →
        2 * ((n : ℝ) ^ 2) * (2 ^ rOut A K n : ℝ) ≤
          (minPile (splitM K n) : ℝ) *
            (((4 : ℝ) / 3) ^ splitA K n))
    (hceilSq :
      ∀ n : ℕ, n0 ≤ n →
        (n : ℝ) ^ 2 ≤ (((4 : ℝ) / 3) ^ splitA K n)) :
    HasRealHypercubePebblingUpperBound
      (Real.exp (4 * loss n0) *
        finiteBaseNormalizedBound (recursiveCostBound K n0) n0) := by sorry
