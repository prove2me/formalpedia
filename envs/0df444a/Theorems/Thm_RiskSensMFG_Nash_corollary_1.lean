-- Prove2me | Theorems.Thm_RiskSensMFG_Nash_corollary_1
-- name    : RiskSensMFG.Nash.corollary_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:46:49.246976+00:00
-- url     : https://prove2.me/theorems/370ac02c-29ed-40bc-ae08-655c90326b35
-- title:
--   Corollary 1, p. 29 — infinite-horizon comparison of the deviating agent's N-agent cost with the equilibrium cost J_µ(π)
-- statement:
--   Let $(\pi,\boldsymbol\mu)$ be a mean-field equilibrium, under the standing assumptions and Assumptions 1 and 2, and let $\{\tilde\pi^{(N)}\}$ be weakly continuous Markov policies for Agent 1. Then:
--
--   1. $J^{(N)}_1(\tilde\pi^{(N)},\pi,\dots,\pi)-J_{\boldsymbol\mu}(\tilde\pi^{(N)})\to0$;
--   2. $J^{(N)}_1(\pi,\dots,\pi)\to J_{\boldsymbol\mu}(\pi)$;
--   3. for every $\delta>0$, eventually in $N$,
--   $$J^{(N)}_1(\tilde\pi^{(N)},\pi,\dots,\pi)\ \ge\ J_{\boldsymbol\mu}(\pi)-\delta=\inf_{\pi'\in\mathsf M}J_{\boldsymbol\mu}(\pi')-\delta .$$
--
--   The paper prints this as $\lim_{N}J^{(N)}_1(\tilde\pi^{(N)},\pi,\dots,\pi)\ge\inf_{\pi'\in\mathsf M}J_{\boldsymbol\mu}(\pi')=J_{\boldsymbol\mu}(\pi)=\lim_NJ^{(N)}_1(\pi,\dots,\pi)$.
--
--   **Formalization Note** The first limit of the printed display is not shown to exist; what the proof gives is the three items above, and the printed "$\lim\ge$" is read as item 3. Sequences are indexed by $N+1$ as in Theorem 4.
-- source:
--   Saldi, Başar & Raginsky, Discrete-time Risk-sensitive Mean-field Games, arXiv:1808.03929v2, p. 29, Corollary 1; proof p. 30

import Mathlib
import Definitions.Def_RiskSensMFG_Nash_Model
import Definitions.Def_RiskSensMFG_Nash_Equilibrium
import Definitions.Def_RiskSensMFG_Nash_Game

open MeasureTheory ProbabilityTheory Filter Topology

namespace RiskSensMFG.Nash

theorem corollary_1 {X A : Type*} [MetricSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace A] [PolishSpace A] [MeasurableSpace A] [BorelSpace A] [CompactSpace A]
    (M : Model X A) (hS : M.Standing) (h1 : Assumption1 M) (h2a : Assumption2a M)
    (π : MarkovPolicy X A) (μ : ℕ → RiskSensMFG.Existence.PM X) (hmfe : IsMFE M π μ) (h2b : π.WeaklyContinuous)
    (πt : ℕ → MarkovPolicy X A) (hπt : ∀ N, (πt N).WeaklyContinuous) :
    Tendsto (fun N : ℕ => JN M (N + 1) (Function.update (fun _ => π) 0 (πt (N + 1))) 0 -
        J M μ (πt (N + 1)).toPolicy) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => JN M (N + 1) (fun _ => π) 0) atTop (𝓝 (J M μ π.toPolicy)) ∧
      ∀ δ > 0, ∀ᶠ N : ℕ in atTop,
        J M μ π.toPolicy - δ ≤ JN M (N + 1) (Function.update (fun _ => π) 0 (πt (N + 1))) 0 := by sorry

end RiskSensMFG.Nash
