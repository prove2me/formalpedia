-- Prove2me | Theorems.Thm_RiskSensMFG_Nash_proposition_10
-- name    : RiskSensMFG.Nash.proposition_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:47:04.58147+00:00
-- url     : https://prove2.me/theorems/ae11a9dd-2456-4f5b-bc23-da8e2fe4b0fd
-- title:
--   Proposition 10, p. 29 — the deviating agent's augmented state law is asymptotically that of the mean-field chain under its policy
-- statement:
--   Let $(\pi,\boldsymbol\mu)$ be a mean-field equilibrium, under the standing assumptions and Assumptions 1 and 2, and let $\{\tilde\pi^{(N)}\}$ be weakly continuous Markov policies. Let $\tilde s^N_1(t)$ be Agent 1's augmented state in the $N$-agent game under $(\tilde\pi^{(N)},\pi,\dots,\pi)$, and $\hat s^N(t)$ the augmented mean-field chain: $\hat s^N(0)\sim\kappa_0$, $\hat s^N(t+1)\sim P^{\tilde\pi^{(N)}}_{t,\Delta_t}(\cdot\mid\hat s^N(t))$. For every $t\ge0$,
--   $$\lim_{N\to\infty}\big|\mathcal L(\tilde s^N_1(t))(g_N)-\mathcal L(\hat s^N(t))(g_N)\big|=0$$
--   for every sequence $\{g_N\}\subset C_b(\mathsf S)$ with $\sup_N\|g_N\|<\infty$ and $\omega_g(r)\to0$ as $r\to0$, where $\omega_g(r)=\sup_{x}\sup_{N}\sup_{|c-c'|\le r}|g_N(x,c)-g_N(x,c')|$.
--
--   **Formalization Note** $\omega_g(r)\to0$ is written without suprema, as "for every $\varepsilon>0$ there is $\delta>0$ with $|g_N(x,c)-g_N(x,c')|\le\varepsilon$ whenever $|c-c'|\le\delta$, for all $x,N$". The sequences $g$ and $\tilde\pi$ are indexed by $\mathbb N$ and the term $N+1$ is used with $N+1$ agents; the bound and modulus conditions are imposed on all terms, which is no restriction (set the unused term $0$ equal to term $1$). The law of $\hat s^N(t)$ is the state marginal of the augmented single-agent model under $\tilde\pi^{(N)}$ and the flow $\boldsymbol\Delta$, which is the same Markov chain.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 29, Proposition 10; ŝ^N on p. 28; proof Appendix C, pp. 34–36

import Mathlib
import Definitions.Def_RiskSensMFG_Nash_Model
import Definitions.Def_RiskSensMFG_Nash_Equilibrium
import Definitions.Def_RiskSensMFG_Nash_Game
import Definitions.Def_RiskSensMFG_Nash_Augmented

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BoundedContinuousFunction

namespace RiskSensMFG.Nash

theorem proposition_10 {X A : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M) (h2a : Assumption2a M)
    (π : MarkovPolicy X A) (μ : ℕ → RiskSensMFG.Existence.PM X) (hmfe : IsMFE M π μ) (h2b : π.WeaklyContinuous)
    (πt : ℕ → MarkovPolicy X A) (hπt : ∀ N, (πt N).WeaklyContinuous) (t : ℕ)
    (g : ℕ → (X × ℝ →ᵇ ℝ)) (hg_bdd : ∃ B : ℝ, ∀ N, ‖g N‖ ≤ B)
    (hg_mod : ∀ ε > 0, ∃ δ > 0, ∀ (x : X) (N : ℕ) (c c' : ℝ), |c - c'| ≤ δ →
      |g N (x, c) - g N (x, c')| ≤ ε) :
    Tendsto (fun N : ℕ =>
        |∫ s, g (N + 1) s ∂((augLawN M hS.measurable_c (N + 1) (Function.update (fun _ => π) 0 (πt (N + 1)))).map
            (fun ω => (ω t 0).1)) -
          ∫ s, g (N + 1) s ∂((augLaw M hS.measurable_c (augFlow M hS.measurable_c μ π)
            (πt (N + 1))).map (fun ω => (ω t).1))|) atTop (𝓝 0) := by sorry

end RiskSensMFG.Nash
