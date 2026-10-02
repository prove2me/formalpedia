-- Prove2me | Theorems.Thm_ScenarioApproach_EmpiricalCosts_worstCost_eq_empiricalCost_d_of_fullySupported
-- name    : ScenarioApproach.EmpiricalCosts.worstCost_eq_empiricalCost_d_of_fullySupported
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T18:25:59.348536+00:00
-- url     : https://prove2.me/theorems/da6cbf0c-8073-4780-9a47-25df9c7ed8e3
-- title:
--   p. 90 — for fully supported problems, ℓ* = ℓ*_d with probability 1
-- statement:
--   Let $\ell(\nu,\delta)$, $\nu\in\mathbb R^{d-1}$, be convex in $\nu$ for every $\delta$, let the scenario program $\min_\nu\max_i\ell(\nu,\delta_i)$ have a unique solution for every sample size $m\ge1$ and every sample, and let the problem be fully supported. Let $\nu^*$ be the solution with $N\ge d$ scenarios drawn independently from $\mathbb P$, $\ell^*=\max_i\ell(\nu^*,\delta_i)$ its optimal value and $\ell^*_d$ its $d$-th empirical cost. Then
--
--   $$
--   \ell^*=\ell^*_d\qquad\text{with probability }1 .
--   $$
--
--   In words: in a fully supported problem at least $d$ scenarios attain the worst-case cost at the solution. In general only $\ell^*\ge\ell^*_d$ holds.
--
--   **Formalization Note** $\nu\in$ `EuclideanSpace ℝ (Fin n)`, $d=n+1$. "With probability 1" is `∀ᵐ` with respect to the product measure $\mathbb P^N$. Existence and uniqueness is required for every $m\ge1$, and measurability of $\ell$ and of the solution map is assumed, as in the other theorems of this mission.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 90 (sentence after Definition 8.3); Definition 5.4, p. 58

import Mathlib
import Definitions.Def_ScenarioApproach_EmpiricalCosts_scenarioProgram
import Definitions.Def_ScenarioApproach_EmpiricalCosts_empiricalCost
import Definitions.Def_ScenarioApproach_EmpiricalCosts_supportConstraint

namespace ScenarioApproach.EmpiricalCosts

/-- p. 90: for fully supported problems (Definition 5.4), `ℓ* = ℓ*_d` with probability 1, where
`ℓ* = max_i ℓ(ν*, δᵢ)` is the optimal value of the scenario program (1.4) with `ν ∈ ℝ^n`,
`d = n + 1`, and `ℓ*_d` is its `d`-th empirical cost. -/
theorem worstCost_eq_empiricalCost_d_of_fullySupported
    {n N : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    -- standing assumption (p. 6): `ℓ(ν, δ)` is convex in `ν` for every `δ`
    (hconv : ∀ δ, ConvexOn ℝ Set.univ fun ν => ℓ ν δ)
    -- measurability, glossed over in the book (p. 6, footnote 1; p. 33)
    (hmeas : Measurable (Function.uncurry ℓ))
    -- Assumption 3.6 for (1.4): existence and uniqueness for every `m ≥ 1` and every sample
    (hexu : ∀ m : ℕ, 1 ≤ m → ∀ ω : Fin m → Δ, ∃! ν, IsSolution ℓ ω ν)
    -- Definition 5.4 for (1.4)
    (hfs : FullySupported P ℓ)
    -- `νstar ω` is the solution `ν*` of the scenario program with the `N` scenarios `ω`
    (νstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin n))
    (hνstar : ∀ ω, IsSolution ℓ ω (νstar ω)) (hνstar_meas : Measurable νstar)
    (hN : n + 1 ≤ N) :
    ∀ᵐ ω ∂(MeasureTheory.Measure.pi fun _ : Fin N => P),
      worstCost ℓ ω (νstar ω) = empiricalCost ℓ ω (νstar ω) (n + 1) := by sorry

end ScenarioApproach.EmpiricalCosts
