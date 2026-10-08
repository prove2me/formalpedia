-- Prove2me | Theorems.Thm_ScenarioApproach_Nonconvex_violation_tail_le_beta
-- name    : ScenarioApproach.Nonconvex.violation_tail_le_beta
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-30T18:46:56.11881+00:00
-- url     : https://prove2.me/theorems/07f2f276-28ca-4a04-b7d8-5a78bd6a85a7
-- title:
--   Eq. (8.16) — with ε(k) of (8.16), ℙ^N{V(θ*) > ε(σ*)} ≤ β
-- statement:
--   Let $\Theta$ be a generic set, $f:\Theta\to\mathbb R$ a cost, $\Theta_\delta\subseteq\Theta$ constraint sets indexed by $\delta\in\Delta$, and $\mathbb P$ a probability on $\Delta$. Let $\delta_1,\dots,\delta_N$ be independent samples from $\mathbb P$; assume that for every sample the scenario program (8.12) has a unique solution $\theta^*$. Let an arbitrary algorithm return, for every sample, a support set (Definition 8.8) of the program, and let $\sigma^*$ be its cardinality. Let $V$ be the violation (Definition 3.1). For any $\beta\in[0,1]$, with $\epsilon(k)$ the function (8.16),
--
--   $$
--   \epsilon(k)=\begin{cases}1 & k=N,\\ 1-\sqrt[N-k]{\beta/\big(N\binom Nk\big)} & \text{otherwise,}\end{cases}
--   $$
--
--   it holds that
--
--   $$
--   \mathbb P^N\{V(\theta^*)>\epsilon(\sigma^*)\}\le\beta.
--   $$
--
--   This makes the support-set result (8.15) usable in practice: after solving the program and finding a support set of cardinality $\sigma^*$, the decision-maker certifies $V(\theta^*)\le\epsilon(\sigma^*)$ with confidence $1-\beta$, with no convexity or nondegeneracy assumption.
--
--   **Formalization Note** The sample is `ω : Fin N → Δ` with law `Measure.pi (fun _ => P)`, and the probability is compared in $[0,\infty]$ with `ENNReal.ofReal β`. The book glosses over measurability (p. 33); the pinned-down form assumes the constraint relation $\{(\theta,\delta):\theta\in\Theta_\delta\}$ is jointly measurable, the solution map $\omega\mapsto\theta^*$ is measurable, and each event $\{\text{the algorithm returns } J\}$ is measurable. The solution $\theta^*$ is assumed to exist and be unique for every sample, and the algorithm to return a support set for every sample. No hypothesis $N\ge1$ is needed: for $N=0$ the event is empty.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 105, Eq. (8.16) (based on Eq. (8.15), p. 104, proven in [31])

import Mathlib
import Definitions.Def_ScenarioApproach_Nonconvex_violation
import Definitions.Def_ScenarioApproach_Nonconvex_scenarioProgram
import Definitions.Def_ScenarioApproach_Nonconvex_supportSet
import Definitions.Def_ScenarioApproach_Nonconvex_epsBeta

namespace ScenarioApproach.Nonconvex

/-- Eq. (8.16). In the setting of (8.15) (nonconvex scenario program (8.12) over a generic set,
`θstar ω` its solution, `alg ω` a support set returned by any algorithm, `σ* = (alg ω).card`),
the function `ε = epsBeta N β` of (8.16) gives `ℙ^N{V(θ*) > ε(σ*)} ≤ β` for every
`β ∈ [0, 1]`. -/
theorem violation_tail_le_beta {Θ Δ : Type*} [MeasurableSpace Θ] [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (f : Θ → ℝ) (Θδ : Δ → Set Θ) (N : ℕ)
    (hmeas : MeasurableSet {p : Θ × Δ | p.1 ∈ Θδ p.2})
    (θstar : (Fin N → Δ) → Θ)
    (hθstar : ∀ ω, IsUniqueSolutionOn f Θδ ω Finset.univ (θstar ω))
    (hθstar_meas : Measurable θstar)
    (alg : (Fin N → Δ) → Finset (Fin N))
    (halg : ∀ ω, IsSupportSet f Θδ ω (alg ω))
    (halg_meas : ∀ J : Finset (Fin N), MeasurableSet {ω | alg ω = J})
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    MeasureTheory.Measure.pi (fun _ : Fin N => P)
        {ω | epsBeta N β (alg ω).card < violation P Θδ (θstar ω)} ≤ ENNReal.ofReal β := by sorry

end ScenarioApproach.Nonconvex
