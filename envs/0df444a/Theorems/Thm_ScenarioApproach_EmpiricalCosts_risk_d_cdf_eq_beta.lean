-- Prove2me | Theorems.Thm_ScenarioApproach_EmpiricalCosts_risk_d_cdf_eq_beta
-- name    : ScenarioApproach.EmpiricalCosts.risk_d_cdf_eq_beta
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T18:29:09.927766+00:00
-- url     : https://prove2.me/theorems/3a129f72-0349-4b2a-8273-3644fe4791d8
-- title:
--   Corollary of Theorem 8.4 — R_d has distribution B(d, N−d+1)
-- statement:
--   Let $\ell(\nu,\delta)$, $\nu\in\mathbb R^{d-1}$, be convex in $\nu$ for every $\delta$, let the scenario program $\min_\nu\max_i\ell(\nu,\delta_i)$ have a unique solution for every sample size $m\ge1$ and every sample, and let it be nondegenerate (Definition 8.3). Let $\nu^*$ be the solution with $N\ge d$ scenarios drawn independently from $\mathbb P$ and $R_d=R(\nu^*,\ell^*_d)$ the risk of its $d$-th empirical cost. Then $R_d$ has the beta distribution $B(d,N-d+1)$: for every $\varepsilon\in[0,1]$,
--
--   $$
--   \mathbb P^N\{R_d\le\varepsilon\}=1-\sum_{i=0}^{d-1}\binom Ni\varepsilon^i(1-\varepsilon)^{N-i}.
--   $$
--
--   Since $\ell^*\ge\ell^*_d$, the risk of $(\nu^*,\ell^*)$ is at most $R_d$, and the bound of Theorem 3.7 is recovered from this exact law.
--
--   **Formalization Note** The beta distribution function is written in the binomial form of the book's Eq. (3.5). $\nu\in$ `EuclideanSpace ℝ (Fin n)`, $d=n+1$; existence and uniqueness for every $m\ge1$ and measurability of $\ell$ and of the solution map are assumed as in the other theorems.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 90 (corollary of Theorem 8.4); p. 39, Eq. (3.5)

import Mathlib
import Definitions.Def_ScenarioApproach_EmpiricalCosts_scenarioProgram
import Definitions.Def_ScenarioApproach_EmpiricalCosts_empiricalCost
import Definitions.Def_ScenarioApproach_EmpiricalCosts_risk
import Definitions.Def_ScenarioApproach_EmpiricalCosts_nondegenerate

namespace ScenarioApproach.EmpiricalCosts

/-- Corollary of Theorem 8.4 (p. 90): under nondegeneracy, `R_d` has the beta distribution
`B(d, N-d+1)`; in the form (3.5) of its distribution function, for `ε ∈ [0, 1]`,
`ℙ^N{R_d ≤ ε} = 1 - ∑_{i=0}^{d-1} (N choose i) ε^i (1-ε)^{N-i}`. Here `ν ∈ ℝ^n`, `d = n + 1`. -/
theorem risk_d_cdf_eq_beta
    {n N : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    -- standing assumption (p. 6): `ℓ(ν, δ)` is convex in `ν` for every `δ`
    (hconv : ∀ δ, ConvexOn ℝ Set.univ fun ν => ℓ ν δ)
    -- measurability, glossed over in the book (p. 6, footnote 1; p. 33)
    (hmeas : Measurable (Function.uncurry ℓ))
    -- Assumption 3.6 for (1.4): existence and uniqueness for every `m ≥ 1` and every sample
    (hexu : ∀ m : ℕ, 1 ≤ m → ∀ ω : Fin m → Δ, ∃! ν, IsSolution ℓ ω ν)
    -- Definition 8.3 (nondegeneracy), for every sample size `m ≥ d`
    (hnd : Nondegenerate P ℓ)
    -- `νstar ω` is the solution `ν*` of the scenario program with the `N` scenarios `ω`
    (νstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin n))
    (hνstar : ∀ ω, IsSolution ℓ ω (νstar ω)) (hνstar_meas : Measurable νstar)
    (hN : n + 1 ≤ N) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin N => P)
        {ω | empiricalRisk P ℓ ω (νstar ω) (n + 1) ≤ ε} =
      ENNReal.ofReal
        (1 - ∑ i ∈ Finset.range (n + 1), (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i)) := by sorry

end ScenarioApproach.EmpiricalCosts
