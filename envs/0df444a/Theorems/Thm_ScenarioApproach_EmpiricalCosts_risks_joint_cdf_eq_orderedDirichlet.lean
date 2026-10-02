-- Prove2me | Theorems.Thm_ScenarioApproach_EmpiricalCosts_risks_joint_cdf_eq_orderedDirichlet
-- name    : ScenarioApproach.EmpiricalCosts.risks_joint_cdf_eq_orderedDirichlet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T18:32:22.834042+00:00
-- url     : https://prove2.me/theorems/1fc44cd9-b640-4ff1-a01f-1d45933f121c
-- title:
--   Theorem 8.4 — the risks R_d, …, R_N have an ordered Dirichlet distribution
-- statement:
--   Let $\ell(\nu,\delta)$, $\nu\in\mathbb R^{d-1}$, be convex in $\nu$ for every $\delta$, and let $\delta_1,\dots,\delta_N$, $N\ge d$, be drawn independently from a probability $\mathbb P$ on $\Delta$. Assume that the scenario program $\min_\nu\max_i\ell(\nu,\delta_i)$ has a unique solution for every sample size $m\ge1$ and every sample, and that it is nondegenerate (Definition 8.3). Let $\nu^*$ be the solution with the $N$ scenarios, $\ell^*_d\ge\cdots\ge\ell^*_N$ its empirical costs from index $d$ on, and $R_k=\mathbb P\{\delta:\ell(\nu^*,\delta)>\ell^*_k\}$ their risks. Then the joint distribution function of $R_d,\dots,R_N$ is the ordered Dirichlet distribution with parameters $(d,1,\dots,1)$ ($N-d$ ones): for all $\varepsilon_d,\dots,\varepsilon_N$,
--
--   $$
--   \mathbb P^N\{R_d\le\varepsilon_d,\dots,R_N\le\varepsilon_N\}=\frac{N!}{(d-1)!}\int_0^{\varepsilon_d}\alpha_d^{d-1}\int_0^{\varepsilon_{d+1}}\cdots\int_0^{\varepsilon_N}\mathbf 1_{\{0\le\alpha_d\le\cdots\le\alpha_N\le1\}}\,\mathrm d\alpha_N\cdots\mathrm d\alpha_{d+1}\,\mathrm d\alpha_d .
--   $$
--
--   The law does not depend on $\ell$ or $\mathbb P$: it is distribution-free. It generalizes Theorem 3.7 (whose risk is dominated by the first marginal) and is used to build a region ("probability box") that contains the whole distribution function of $\ell(\nu^*,\delta)$ with high confidence.
--
--   **Formalization Note** $\nu\in$ `EuclideanSpace ℝ (Fin n)`, $d=n+1$. The right-hand side is `orderedDirichletCDF`, a Lebesgue integral over the box $\prod_k[0,\varepsilon_k]$; the identity is stated for all real $\varepsilon_k$ (both sides vanish when some $\varepsilon_k<0$ and are unchanged when $\varepsilon_k>1$ is replaced by $1$). Existence and uniqueness is required for every $m\ge1$ (the program with no scenario has no solution); nondegeneracy is required for every sample size $m\ge d$, as in Definition 8.3; $\ell$ is jointly measurable and the solution map is measurable.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 90, Theorem 8.4

import Mathlib
import Definitions.Def_ScenarioApproach_EmpiricalCosts_scenarioProgram
import Definitions.Def_ScenarioApproach_EmpiricalCosts_empiricalCost
import Definitions.Def_ScenarioApproach_EmpiricalCosts_risk
import Definitions.Def_ScenarioApproach_EmpiricalCosts_nondegenerate
import Definitions.Def_ScenarioApproach_EmpiricalCosts_orderedDirichletCDF

namespace ScenarioApproach.EmpiricalCosts

/-- Theorem 8.4 (p. 90): for the scenario program (1.4) with `ν ∈ ℝ^n`, `d = n + 1`, `N ≥ d`,
under nondegeneracy (Definition 8.3), the joint distribution function of the risks
`R_d, …, R_N` of the empirical costs `ℓ*_d ≥ ⋯ ≥ ℓ*_N` is the ordered Dirichlet distribution with
parameters `(d, 1, …, 1)`:
`ℙ^N{R_d ≤ ε_d, …, R_N ≤ ε_N} = N!/(d-1)! ∫_0^{ε_d} α_d^{d-1} ∫_0^{ε_{d+1}} ⋯ ∫_0^{ε_N}
1_{0 ≤ α_d ≤ ⋯ ≤ α_N ≤ 1} dα_N ⋯ dα_d`. -/
theorem risks_joint_cdf_eq_orderedDirichlet
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
    (hN : n + 1 ≤ N) (ε : ℕ → ℝ) :
    MeasureTheory.Measure.pi (fun _ : Fin N => P)
        {ω | ∀ k : ℕ, n + 1 ≤ k → k ≤ N → empiricalRisk P ℓ ω (νstar ω) k ≤ ε k} =
      ENNReal.ofReal (orderedDirichletCDF (n + 1) N ε) := by sorry

end ScenarioApproach.EmpiricalCosts
