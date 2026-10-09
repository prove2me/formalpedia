-- Prove2me | Theorems.Thm_RobustSAA_Convergence_proposition_4
-- name    : RobustSAA.Convergence.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:18:27.808654+00:00
-- url     : https://prove2.me/theorems/1cbdf25c-e5e1-4ca6-997a-c9b347e8fc0e
-- title:
--   Proposition 4 (first sentence), p. 13 — a uniformly consistent test is consistent
-- statement:
--   Let $N\mapsto\mathcal F_N$ be a DUS map on $\Xi\subseteq\mathbb R^d$ whose sets are all nonempty and such that each rejection event $\{(\xi^1,\dots,\xi^N):F_0\notin\mathcal F_N\}$ is measurable. If the test with confidence regions $\mathcal F_N$ is uniformly consistent, then it is consistent: for every data-generating $F$ and every $F_0\neq F$,
--   $$\lim_{N\to\infty}\mathbb P\big(F_0\notin\mathcal F_N\big)=1 .$$
--
--   Uniform consistency is thus a strengthening of the classical notion of consistency of a goodness-of-fit test (the paper also shows the strengthening is strict; that part is not stated here).
--
--   **Formalization Note** Two hypotheses are added. Measurability of the rejection event: $\mathbb P(F_0\notin\mathcal F_N)$ presupposes it, and the step "a.s. convergence implies convergence in probability" (§10.4, p. 35) needs it. Nonemptiness of every $\mathcal F_N$: the paper's proof picks $F_N\in\mathcal F_N$ for all $N$; without it the map with $\mathcal F_N=\emptyset$ for odd $N$ and $\mathcal F_N=\mathcal P(\Xi)$ for even $N$ is uniformly consistent but not consistent.
-- source:
--   Bertsimas, Gupta, Kallus, Robust Sample Average Approximation, arXiv:1408.4445v3, Proposition 4 (first sentence), p. 13; proof §10.4, p. 35

import Mathlib
import Definitions.Def_RobustSAA_Convergence_Setting
import Definitions.Def_RobustSAA_Convergence_Consistency

open MeasureTheory Filter Topology

namespace RobustSAA.Convergence

theorem proposition_4 {d : ℕ} {Ξ : Set (Pt d)} (𝓕 : DUS Ξ)
    (hne : ∀ (N : ℕ) (s : Fin N → ↥Ξ), (𝓕 N s).Nonempty)
    (hmeas : ∀ (N : ℕ) (F₀ : ProbabilityMeasure ↥Ξ),
      MeasurableSet {s : Fin N → ↥Ξ | F₀ ∉ 𝓕 N s})
    (h𝓕 : IsUniformlyConsistent 𝓕) :
    IsConsistent 𝓕 := by sorry

end RobustSAA.Convergence
