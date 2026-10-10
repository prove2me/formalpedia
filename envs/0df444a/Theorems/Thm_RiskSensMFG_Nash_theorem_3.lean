-- Prove2me | Theorems.Thm_RiskSensMFG_Nash_theorem_3
-- name    : RiskSensMFG.Nash.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:45.729424+00:00
-- url     : https://prove2.me/theorems/15aeefc0-6f24-4396-8f24-8b2127a2d42b
-- title:
--   Theorem 3, p. 23 — for every ε > 0 there is N(ε) such that (π, …, π) is an ε-Markov-Nash equilibrium of the N-agent game for N ≥ N(ε)
-- statement:
--   Let $\mathsf X$ be a Polish metric space and $\mathsf A$ a compact Polish space. Assume the standing assumptions ($\beta\in(0,1)$, $\lambda>0$, $c\ge0$ measurable), Assumption 1, and Assumption 2: (a) the moduli $\omega_p,\omega_c$ of $p$ and $c$ in the measure argument tend to $0$, and (b) each $\pi_t:\mathsf X\to\mathcal P(\mathsf A)$ is weakly continuous, where $(\pi,\boldsymbol\mu)$ is a mean-field equilibrium. Then for every $\varepsilon>0$ there is $N(\varepsilon)$ such that for every $N\ge N(\varepsilon)$ the policy
--   $$\boldsymbol\pi^{(N)}=(\pi,\dots,\pi)$$
--   is an $\varepsilon$-Markov-Nash equilibrium of the game with $N$ agents: for every agent $i$,
--   $$J^{(N)}_i(\boldsymbol\pi^{(N)})\le\inf_{\pi^i\in\mathsf M_i}J^{(N)}_i(\boldsymbol\pi^{(N)}_{-i},\pi^i)+\varepsilon .$$
--
--   This is the paper's approximation theorem: the equilibrium of the infinite-population limit gives approximately optimal decentralized Markov policies for every large finite population, for the risk-sensitive (exponential-utility) criterion.
--
--   **Formalization Note** $\varepsilon$ is on the scale of $J^{(N)}_i=E[e^{\lambda\sum\beta^tc}]$, as in Definition 2. Deviations range over all (measurable) Markov policies. Optimality in the mean-field equilibrium is required only against Markov policies, which makes this statement at least as strong as the printed one.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 23, Theorem 3 (standing setting p. 22, Assumption 2 p. 23); proof pp. 24–30

import Mathlib
import Definitions.Def_RiskSensMFG_Nash_Model
import Definitions.Def_RiskSensMFG_Nash_Equilibrium
import Definitions.Def_RiskSensMFG_Nash_Game

open MeasureTheory ProbabilityTheory Filter Topology

namespace RiskSensMFG.Nash

theorem theorem_3 {X A : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M) (h2a : Assumption2a M)
    (π : MarkovPolicy X A) (μ : ℕ → RiskSensMFG.Existence.PM X) (hmfe : IsMFE M π μ) (h2b : π.WeaklyContinuous) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, IsEpsMarkovNash M N (fun _ => π) ε := by sorry

end RiskSensMFG.Nash
