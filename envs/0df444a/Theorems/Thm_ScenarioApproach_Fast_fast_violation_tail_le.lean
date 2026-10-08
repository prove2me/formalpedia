-- Prove2me | Theorems.Thm_ScenarioApproach_Fast_fast_violation_tail_le
-- name    : ScenarioApproach.Fast.fast_violation_tail_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T05:19:37.855762+00:00
-- url     : https://prove2.me/theorems/fde66c44-bb83-4ce5-93ad-04e99f06043f
-- title:
--   Theorem 8.5 — violation bound of FAST, Eq. (8.5)
-- statement:
--   Let $\ell(\nu,\delta)$ be a loss that is convex in $\nu\in\mathbb R^{d-1}$ for every $\delta\in\Delta$, let $\mathbb P$ be a probability measure on $\Delta$, and assume that for every $m\ge1$ and every sample of $m$ scenarios the scenario program (1.4) has exactly one solution (Assumption 3.6). Draw $N_1+N_2$ independent scenarios $\delta_1,\dots,\delta_{N_1+N_2}$ from $\mathbb P$, with $N_1\ge1$, and run FAST:
--
--   1. solve (1.4) with the first $N_1$ scenarios, obtaining $\nu^*_{N_1}$;
--   2. set $\nu^*_F=\nu^*_{N_1}$ and $\ell^*_F=\max_{i=1,\dots,N_1+N_2}\ell(\nu^*_{N_1},\delta_i)$.
--
--   Then, for every $\varepsilon\in[0,1]$, the violation $V(\nu^*_F,\ell^*_F)=\mathbb P\{\delta:\ \ell(\nu^*_F,\delta)>\ell^*_F\}$ satisfies
--
--   $$
--   \mathbb P^{N_1+N_2}\{V(\nu^*_F,\ell^*_F)>\varepsilon\}\ \le\ (1-\varepsilon)^{N_2}\cdot\sum_{i=0}^{d-1}\binom{N_1}{i}\varepsilon^i(1-\varepsilon)^{N_1-i}.
--   \tag{8.5}
--   $$
--
--   The first stage alone carries the beta bound of Theorem 3.7 with $N_1$ scenarios; the detuning step multiplies it by $(1-\varepsilon)^{N_2}$. This is what lets FAST reach a prescribed confidence with a number of scenarios that is additive, not multiplicative, in $d$ and $1/\varepsilon$.
--
--   **Formalization Note** The book's $d$ is $n+1$ with $\nu\in$ `EuclideanSpace ℝ (Fin n)`. No condition $N_1\ge d$ is imposed, as in the book: for $N_1<d$ the sum equals $1$. The violation is the risk $R$ of Definition 8.2. Hypotheses the book leaves implicit are explicit: the loss is jointly measurable, the first-stage solution map is measurable, $N_1\ge1$ (`NeZero N₁`), and existence and uniqueness are required for every nonempty sample.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 94, Theorem 8.5, Eq. (8.5)

import Mathlib
import Definitions.Def_ScenarioApproach_Fast_scenarioProgram
import Definitions.Def_ScenarioApproach_EmpiricalCosts_risk
import Definitions.Def_ScenarioApproach_Fast_fast

namespace ScenarioApproach.Fast

/-- Theorem 8.5 (p. 94). FAST solves the scenario program (1.4) with the first `N₁` scenarios,
returns `ν*_F = ν*_{N₁}` and the detuned cost `ℓ*_F = max_{i ≤ N₁+N₂} ℓ(ν*_{N₁}, δᵢ)`; with
`d = n + 1`,
`ℙ^{N₁+N₂}{V(ν*_F, ℓ*_F) > ε} ≤ (1-ε)^{N₂} ∑_{i=0}^{d-1} (N₁ choose i) ε^i (1-ε)^{N₁-i}`. -/
theorem fast_violation_tail_le
    {n N₁ N₂ : ℕ} [NeZero N₁] {Δ : Type*} [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (ℓ : EuclideanSpace ℝ (Fin n) → Δ → ℝ)
    -- standing assumption (p. 6): `ℓ(·, δ)` is convex for every `δ`
    (hconv : ∀ δ, ConvexOn ℝ Set.univ (fun ν => ℓ ν δ))
    -- Assumption 3.6 (existence and uniqueness), for every nonempty sample
    (hexu : ∀ (m : ℕ) [NeZero m] (ω : Fin m → Δ), ∃! ν, IsSolution ℓ ω ν)
    -- measurability, glossed over in the book (p. 6, footnote 1; p. 33)
    (hmeas : Measurable (Function.uncurry ℓ))
    -- `νstar ω₁` is the solution `ν*_{N₁}` of the scenario program with the `N₁` scenarios `ω₁`
    (νstar : (Fin N₁ → Δ) → EuclideanSpace ℝ (Fin n))
    (hνstar : ∀ ω₁, IsSolution ℓ ω₁ (νstar ω₁)) (hνstar_meas : Measurable νstar)
    (ε : ℝ) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin (N₁ + N₂) => P)
        {ω | ε < ScenarioApproach.EmpiricalCosts.risk P ℓ (fastDecision νstar ω) (fastCost ℓ νstar ω)} ≤
      ENNReal.ofReal ((1 - ε) ^ N₂ *
        ∑ i ∈ Finset.range (n + 1), (N₁.choose i : ℝ) * ε ^ i * (1 - ε) ^ (N₁ - i)) := by sorry

end ScenarioApproach.Fast
