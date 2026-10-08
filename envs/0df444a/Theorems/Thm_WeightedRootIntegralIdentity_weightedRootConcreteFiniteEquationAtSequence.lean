-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weightedRootConcreteFiniteEquationAtSequence
-- name    : WeightedRootIntegralIdentity.weightedRootConcreteFiniteEquationAtSequence
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T08:29:39.576322+00:00
-- url     : https://prove2.me/theorems/f368fc20-c41d-4e45-8c84-ce170b7e2b70
-- title:
--   Concrete finite-contour equation at the canonical sequence
-- statement:
--   For the canonical truncations εₘ=1/(m+1) and Hₘ=m+1, if the actual six finite weighted-root contour components decompose the boundary integral and the boundary integral equals the fixed residue value ρ at every m, then their oriented sum equals ρ at every m.

import Mathlib
import Definitions.Def_weightedRootFiniteContourComponentsV2
open scoped BigOperators Interval
namespace WeightedRootIntegralIdentity
theorem weightedRootConcreteFiniteEquationAtSequence
    (n : ℕ) (a w : ℕ → ℝ) (a₀ a₁ : ℝ) (ρ : ℂ)
    (hdecomp : ∀ m : ℕ,
      weightedRootBoundaryIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ)) (m + 1 : ℝ) =
        weightedRootFiniteUpperBankIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ)) +
        weightedRootFiniteLowerBankIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ)) +
        weightedRootRightVerticalIntegral n a w a₁ (1 / (m + 1 : ℝ)) (m + 1 : ℝ) +
        weightedRootLeftVerticalIntegral n a w a₀ (1 / (m + 1 : ℝ)) (m + 1 : ℝ) +
        weightedRootFiniteInnerArcIntegral n a w (1 / (m + 1 : ℝ)) +
        weightedRootFiniteOuterArcIntegral n a w (m + 1 : ℝ))
    (hres : ∀ m : ℕ,
      weightedRootBoundaryIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ)) (m + 1 : ℝ) = ρ) :
    ∀ m : ℕ,
      weightedRootFiniteUpperBankIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ)) +
      weightedRootFiniteLowerBankIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ)) +
      weightedRootRightVerticalIntegral n a w a₁ (1 / (m + 1 : ℝ)) (m + 1 : ℝ) +
      weightedRootLeftVerticalIntegral n a w a₀ (1 / (m + 1 : ℝ)) (m + 1 : ℝ) +
      weightedRootFiniteInnerArcIntegral n a w (1 / (m + 1 : ℝ)) +
      weightedRootFiniteOuterArcIntegral n a w (m + 1 : ℝ) = ρ := by sorry
end WeightedRootIntegralIdentity
