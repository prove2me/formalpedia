-- Prove2me | Theorems.Thm_ScenarioApproach_EmpiricalCosts_worst_risk_tail_le_binomial_sum
-- name    : ScenarioApproach.EmpiricalCosts.worst_risk_tail_le_binomial_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T18:21:07.981985+00:00
-- url     : https://prove2.me/theorems/adc66a56-7e49-43e1-8125-9963427f775a
-- title:
--   Theorem 3.7 for (1.4) — the risk R(ν*, ℓ*) is dominated by B(d, N−d+1)
-- statement:
--   Let $\ell(\nu,\delta)$, $\nu\in\mathbb R^{d-1}$, be convex in $\nu$ for every $\delta$, let $\delta_1,\dots,\delta_N$ be drawn independently from a probability $\mathbb P$ on $\Delta$ with $N\ge d$, and assume that the scenario program $\min_\nu\max_{i}\ell(\nu,\delta_i)$ has a unique solution for every sample size $m\ge1$ and every sample. Let $\nu^*$ be its solution with the $N$ scenarios and $\ell^*$ its optimal value. Then for every $\varepsilon\in[0,1]$
--
--   $$
--   \mathbb P^N\{R(\nu^*,\ell^*)>\varepsilon\}\ \le\ \sum_{i=0}^{d-1}\binom Ni\varepsilon^i(1-\varepsilon)^{N-i},
--   $$
--
--   that is, the distribution of the risk $R(\nu^*,\ell^*)=\mathbb P\{\delta:\ell(\nu^*,\delta)>\ell^*\}$ is dominated by the beta distribution $B(d,N-d+1)$.
--
--   This is the generalization theorem of the scenario approach, Theorem 3.7 of the book, read for the min-max program through its epigraph form, in which $R(\nu^*,\ell^*)$ is the violation probability of $(\nu^*,\ell^*)$. Theorem 8.4 refines it to an exact law for all the empirical costs.
--
--   **Formalization Note** $\nu\in$ `EuclideanSpace ℝ (Fin n)` and $d=n+1$. Existence and uniqueness (the book's Assumption 3.6) is required for every $m\ge1$: for $m=0$ the epigraph program is unbounded, so the book's "for every $m$" cannot be meant there. Measurability, glossed over in the book, is assumed: $(\nu,\delta)\mapsto\ell(\nu,\delta)$ is jointly measurable and the solution map $\omega\mapsto\nu^*$ is measurable. The probability is compared in $[0,\infty]$ with `ENNReal.ofReal` of the right-hand side.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 90 (application of Theorem 3.7); p. 39, Theorem 3.7, Eq. (3.4)

import Mathlib
import Definitions.Def_ScenarioApproach_EmpiricalCosts_scenarioProgram
import Definitions.Def_ScenarioApproach_EmpiricalCosts_risk

namespace ScenarioApproach.EmpiricalCosts

/-- Theorem 3.7 for the scenario program (1.4), `ν ∈ ℝ^n`, `d = n + 1` (p. 90): the distribution
of `R(ν*, ℓ*)` is dominated by the beta distribution `B(d, N-d+1)`, i.e. for `N ≥ d`,
`ℙ^N{R(ν*, ℓ*) > ε} ≤ ∑_{i=0}^{d-1} (N choose i) ε^i (1-ε)^{N-i}`. -/
theorem worst_risk_tail_le_binomial_sum
    {n N : ℕ} {Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    -- standing assumption (p. 6): `ℓ(ν, δ)` is convex in `ν` for every `δ`
    (hconv : ∀ δ, ConvexOn ℝ Set.univ fun ν => ℓ ν δ)
    -- measurability, glossed over in the book (p. 6, footnote 1; p. 33)
    (hmeas : Measurable (Function.uncurry ℓ))
    -- Assumption 3.6 for (1.4): existence and uniqueness for every `m ≥ 1` and every sample
    (hexu : ∀ m : ℕ, 1 ≤ m → ∀ ω : Fin m → Δ, ∃! ν, IsSolution ℓ ω ν)
    -- `νstar ω` is the solution `ν*` of the scenario program with the `N` scenarios `ω`
    (νstar : (Fin N → Δ) → EuclideanSpace ℝ (Fin n))
    (hνstar : ∀ ω, IsSolution ℓ ω (νstar ω)) (hνstar_meas : Measurable νstar)
    (hN : n + 1 ≤ N) (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin N => P)
        {ω | ε < risk P ℓ (νstar ω) (worstCost ℓ ω (νstar ω))} ≤
      ENNReal.ofReal
        (∑ i ∈ Finset.range (n + 1), (N.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N - i)) := by sorry

end ScenarioApproach.EmpiricalCosts
