-- Prove2me | Theorems.Thm_ScenarioApproach_Fast_risk_tail_le_binomial_sum
-- name    : ScenarioApproach.Fast.risk_tail_le_binomial_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T04:49:01.568392+00:00
-- url     : https://prove2.me/theorems/e130b017-737f-4ae3-95e1-51893fa82ad9
-- title:
--   Theorem 3.7 for program (1.4) — R(ν*, ℓ*) is dominated by B(d, N−d+1)
-- statement:
--   Let $\ell(\nu,\delta)$ be a loss that is convex in $\nu\in\mathbb R^{d-1}$ for every $\delta\in\Delta$, let $\mathbb P$ be a probability measure on $\Delta$, and let $\delta_1,\dots,\delta_N$ be independent samples from $\mathbb P$. Assume that for every $m\ge1$ and every sample of $m$ scenarios the scenario program (1.4) has exactly one solution (Assumption 3.6), and let $\nu^*$ be the solution and $\ell^*$ the optimal value of the program with the $N$ scenarios. If $N\ge d$, then for every $\varepsilon\in[0,1]$
--
--   $$
--   \mathbb P^N\{R(\nu^*,\ell^*)>\varepsilon\}\ \le\ \sum_{i=0}^{d-1}\binom{N}{i}\varepsilon^i(1-\varepsilon)^{N-i},
--   $$
--
--   where $R$ is the risk of Definition 8.2. Equivalently, the distribution of $R(\nu^*,\ell^*)$ is dominated by the beta distribution $B(d,N-d+1)$.
--
--   This is Theorem 3.7 of the book applied to the epigraphic form of (1.4), whose $d$ optimization variables are $(\nu,\ell)$. It is the first-stage guarantee of FAST: the second factor on the right-hand side of (8.5).
--
--   **Formalization Note** The book's $d$ is $n+1$ with $\nu\in$ `EuclideanSpace ℝ (Fin n)`. Hypotheses the book leaves implicit are explicit: the loss is jointly measurable, the solution map is measurable, and existence and uniqueness are required for every nonempty sample (the program without scenarios has no minimum). The sample law is `Measure.pi (fun _ : Fin N => P)`, and the probability is compared in `ℝ≥0∞` with `ENNReal.ofReal` of the binomial sum.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 90 (recalling Theorem 3.7, p. 39, Eq. (3.4)); Assumption 3.6, p. 38

import Mathlib
import Definitions.Def_ScenarioApproach_Fast_scenarioProgram
import Definitions.Def_ScenarioApproach_EmpiricalCosts_risk

namespace ScenarioApproach.Fast

/-- Theorem 3.7 (p. 39) for the scenario program (1.4), as recalled on p. 90: with
`d = n + 1` optimization variables `(ν, ℓ)` and `N ≥ d` scenarios, the ScenarioApproach.EmpiricalCosts.risk `R(ν*, ℓ*)` of the
solution and its optimal value is dominated by a beta distribution `B(d, N - d + 1)`:
`ℙ^N{R(ν*, ℓ*) > ε} ≤ ∑_{i=0}^{d-1} (N choose i) ε^i (1-ε)^{N-i}`. -/
theorem risk_tail_le_binomial_sum
    {n N : ℕ} [NeZero N] {Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    -- standing assumption (p. 6): `ℓ(·, δ)` is convex for every `δ`
    (hconv : ∀ δ, ConvexOn ℝ Set.univ (fun ν => ℓ ν δ))
    -- Assumption 3.6 (existence and uniqueness), for every nonempty sample
    (hexu : ∀ (m : ℕ) [NeZero m] (ω : Fin m → Δ), ∃! ν, IsSolution ℓ ω ν)
    -- measurability, glossed over in the book (p. 6, footnote 1; p. 33)
    (hmeas : Measurable (Function.uncurry ℓ))
    -- `νstar ω` is the solution `ν*` of the scenario program with the `N` scenarios `ω`
    (νstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin n))
    (hνstar : ∀ ω, IsSolution ℓ ω (νstar ω)) (hνstar_meas : Measurable νstar)
    (hN : n + 1 ≤ N) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin N => P)
        {ω | ε < ScenarioApproach.EmpiricalCosts.risk P ℓ (νstar ω) (scenarioCost ℓ ω (νstar ω))} ≤
      ENNReal.ofReal
        (∑ i ∈ Finset.range (n + 1), (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i)) := by sorry

end ScenarioApproach.Fast
