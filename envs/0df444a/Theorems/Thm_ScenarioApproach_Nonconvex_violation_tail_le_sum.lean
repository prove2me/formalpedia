-- Prove2me | Theorems.Thm_ScenarioApproach_Nonconvex_violation_tail_le_sum
-- name    : ScenarioApproach.Nonconvex.violation_tail_le_sum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T18:48:26.035253+00:00
-- url     : https://prove2.me/theorems/aa4799e3-6f26-432c-96a9-8c6b53017a2a
-- title:
--   Eq. (8.15) — ℙ^N{V(θ*) > ε(σ*)} ≤ ∑_{k<N} (N choose k)(1 − ε(k))^{N−k} for any support-set algorithm
-- statement:
--   This is the support-set bound for nonconvex scenario optimization, stated in Campi and Garatti's book as Eq. (8.15) and proven in [31] (M. C. Campi, S. Garatti, F. A. Ramponi, *A general scenario theory for nonconvex optimization and decision making*, IEEE Trans. Automatic Control, 2018).
--
--   Let $\Theta$ be a generic set (no algebraic or topological structure is required), $f:\Theta\to\mathbb R$ a cost, and $\Theta_\delta\subseteq\Theta$ constraint sets indexed by an uncertain parameter $\delta\in\Delta$, where $\Delta$ carries a probability $\mathbb P$. No convexity is assumed. Let $\delta_1,\dots,\delta_N$ be independent samples from $\mathbb P$, and assume that for every sample the scenario program
--
--   $$
--   \min_{\theta\in\Theta}f(\theta)\quad\text{subject to}\quad\theta\in\bigcap_{i=1,\dots,N}\Theta_{\delta_i}\qquad(8.12)
--   $$
--
--   has a unique solution $\theta^*$. Let $\sigma^*$ be the cardinality of a support set (Definition 8.8) obtained by any algorithm, so the support set need be neither minimal nor irreducible. Let $V(\theta)=\mathbb P\{\delta:\theta\notin\Theta_\delta\}$ be the violation. Then for every function $\epsilon:\{0,1,\dots,N\}\to[0,1]$ with $\epsilon(N)=1$,
--
--   $$
--   \mathbb P^N\{V(\theta^*)>\epsilon(\sigma^*)\}\le\sum_{k=0}^{N-1}\binom Nk\,(1-\epsilon(k))^{N-k}.
--   $$
--
--   The result certifies the violation of the solution of a nonconvex program from a quantity observed after solving it, the size of a support set, without any nondegeneracy assumption. With the particular choice (8.16) of $\epsilon$ the right-hand side equals a prescribed confidence parameter $\beta$.
--
--   **Formalization Note** The sample is `ω : Fin N → Δ` with law `Measure.pi (fun _ => P)`; the probability is compared in $[0,\infty]$ with `ENNReal.ofReal` of the real right-hand side. The algorithm is an arbitrary map `alg` from samples to subsets of `Fin N` that returns a support set for every sample, and $\sigma^*$ is the cardinality of its output; the theorem is universal over such maps. $\epsilon$ is a function `ℕ → ℝ` constrained on $\{0,\dots,N\}$ only. The book glosses over measurability (p. 33); the pinned-down form assumes the constraint relation $\{(\theta,\delta):\theta\in\Theta_\delta\}$ is jointly measurable (with a measurable structure on $\Theta$), the solution map $\omega\mapsto\theta^*$ is measurable, and every event $\{\text{the algorithm returns } J\}$ is measurable. Existence and uniqueness of $\theta^*$ are assumed for the full program and every sample, not for the reduced programs.
-- source:
--   Campi & Garatti, Introduction to the Scenario Approach, SIAM/MOS 2018, DOI 10.1137/1.9781611975444, p. 104, Eq. (8.15) (proven in [31], Campi, Garatti, Ramponi, IEEE TAC 2018); setting p. 102, Eq. (8.12); Definition 8.8, p. 104

import Mathlib
import Definitions.Def_ScenarioApproach_Nonconvex_violation
import Definitions.Def_ScenarioApproach_Nonconvex_scenarioProgram
import Definitions.Def_ScenarioApproach_Nonconvex_supportSet

namespace ScenarioApproach.Nonconvex

/-- Eq. (8.15) (proven in [31], Campi–Garatti–Ramponi 2018). Nonconvex scenario program (8.12)
over a generic set `Θ` with cost `f` and constraints `Θδ`. `θstar ω` is the solution with the
`N` sampled constraints `ω`, and `alg` is any algorithm returning a support set
(Definition 8.8) `alg ω` for every sample; `σ* = (alg ω).card`. For every
`ε : {0, …, N} → [0, 1]` with `ε(N) = 1`,
`ℙ^N{V(θ*) > ε(σ*)} ≤ ∑_{k=0}^{N−1} (N choose k) (1 − ε(k))^{N−k}`. -/
theorem violation_tail_le_sum {Θ Δ : Type*} [MeasurableSpace Θ] [MeasurableSpace Δ]
    (P : MeasureTheory.Measure Δ) [MeasureTheory.IsProbabilityMeasure P]
    (f : Θ → ℝ) (Θδ : Δ → Set Θ) (N : ℕ)
    (hmeas : MeasurableSet {p : Θ × Δ | p.1 ∈ Θδ p.2})
    (θstar : (Fin N → Δ) → Θ)
    (hθstar : ∀ ω, IsUniqueSolutionOn f Θδ ω Finset.univ (θstar ω))
    (hθstar_meas : Measurable θstar)
    (alg : (Fin N → Δ) → Finset (Fin N))
    (halg : ∀ ω, IsSupportSet f Θδ ω (alg ω))
    (halg_meas : ∀ J : Finset (Fin N), MeasurableSet {ω | alg ω = J})
    (ε : ℕ → ℝ) (hε : ∀ k ≤ N, ε k ∈ Set.Icc (0 : ℝ) 1) (hεN : ε N = 1) :
    MeasureTheory.Measure.pi (fun _ : Fin N => P)
        {ω | ε (alg ω).card < violation P Θδ (θstar ω)} ≤
      ENNReal.ofReal (∑ k ∈ Finset.range N, (N.choose k : ℝ) * (1 - ε k) ^ (N - k)) := by sorry

end ScenarioApproach.Nonconvex
