-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_weightedRootInstantiateAndPassFiniteSequenceV3
-- name    : WeightedRootIntegralIdentity.weightedRootInstantiateAndPassFiniteSequenceV3
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-20T09:08:31.360203+00:00
-- url     : https://prove2.me/theorems/c1e1a327-8b19-4618-9160-b9129c220e23
-- title:
--   Instantiate and pass the canonical finite-contour sequence
-- statement:
--   Under the concrete six-component decomposition and the normalized residue balance at the canonical truncations, the accepted sequence-limit theorem yields U+L=rho.

import Mathlib
import Definitions.Def_weightedRootFiniteContourComponentsV2
import Theorems.Thm_WeightedRootIntegralIdentity_weightedRootConcreteFiniteSequenceLimit
import Theorems.Thm_WeightedRootIntegralIdentity_weightedRootFiniteContourResidueEquation
open Filter Topology
open scoped BigOperators Interval

theorem WeightedRootIntegralIdentity.weightedRootInstantiateAndPassFiniteSequenceV3
    (n : ℕ) (a w : ℕ → ℝ) (a₀ a₁ : ℝ) (U L ρ : ℂ)
    (hu : Tendsto (fun m : ℕ =>
      weightedRootFiniteUpperBankIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ))) atTop (𝓝 U))
    (hl : Tendsto (fun m : ℕ =>
      weightedRootFiniteLowerBankIntegral n a w a₀ a₁ (1 / (m + 1 : ℝ))) atTop (𝓝 L))
    (hvr : Tendsto (fun m : ℕ =>
      weightedRootRightVerticalIntegral n a w a₁ (1 / (m + 1 : ℝ)) (m + 1 : ℝ)) atTop (𝓝 0))
    (hvl : Tendsto (fun m : ℕ =>
      weightedRootLeftVerticalIntegral n a w a₀ (1 / (m + 1 : ℝ)) (m + 1 : ℝ)) atTop (𝓝 0))
    (hi : Tendsto (fun m : ℕ =>
      weightedRootFiniteInnerArcIntegral n a w (1 / (m + 1 : ℝ))) atTop (𝓝 0))
    (ho : Tendsto (fun m : ℕ =>
      weightedRootFiniteOuterArcIntegral n a w (m + 1 : ℝ)) atTop (𝓝 0))
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
    U + L = ρ := by
  apply WeightedRootIntegralIdentity.weightedRootConcreteFiniteSequenceLimit n a w a₀ a₁ U L ρ hu hl hvr hvl hi ho
  intro m
  rw [← hdecomp m]
  exact hres m
