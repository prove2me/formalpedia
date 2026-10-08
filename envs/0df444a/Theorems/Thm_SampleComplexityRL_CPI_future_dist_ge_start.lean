-- Prove2me | Theorems.Thm_SampleComplexityRL_CPI_future_dist_ge_start
-- name    : SampleComplexityRL.CPI.future_dist_ge_start
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:12:52.830773+00:00
-- url     : https://prove2.me/theorems/626d57f6-93d3-462a-a4cf-9d40f1ff8f8f
-- title:
--   §7.3.1, p. 88 — the future state distribution dominates the start distribution: $d_{\pi,\mu}\ge\mu/H$
-- statement:
--   Let $S$ and $A$ be finite nonempty sets, $P(\cdot\mid s,a)$ a transition kernel on $S$, $0\le\gamma<1$, $\pi$ a stationary policy and $\mu$ a distribution on $S$. Let $H=1/(1-\gamma)$ be the horizon time and $d_{\pi,\mu}(s)=(1-\gamma)\sum_{t\ge0}\gamma^t\Pr(s_t=s\mid\pi,s_0\sim\mu)$ the discounted future state distribution. Then for every state $s$,
--   $$d_{\pi,\mu}(s)\ \ge\ \frac{\mu(s)}{H}=(1-\gamma)\,\mu(s).$$
--
--   The future distribution keeps a $\mu/H$ contribution from the starting distribution. This converts a guarantee on future advantages, which weight states by $d_{\pi,\mu}$, into information about states weighted by $\mu$.
--
--   **Formalization Note** The point of the statement is pointwise domination by the time-$0$ term of the series; no reward function enters.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 88, Section 7.3.1 (the fact d_{π,μ} ≥ μ/H)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_ApproxOptRL_Shared_Model
import Definitions.Def_ApproxOptRL_CPI_PolicyAdvantage
import Definitions.Def_SampleComplexityRL_CPI_ExactCPI
open ApproxOptRL.Shared ApproxOptRL.CPI FoundationsML.ReinforcementLearning

namespace SampleComplexityRL.CPI

/-- Kakade 2003, §7.3.1, p. 88: the future state distribution dominates the start distribution,
`d_{π,μ} ≥ μ/H` with `H = 1/(1 − γ)`, i.e. `d_{π,μ}(s) ≥ (1 − γ) μ(s)` for every state `s`. -/
theorem future_dist_ge_start {S A : Type} [Fintype S] [DecidableEq S] [Fintype A]
    [Nonempty S] [Nonempty A]
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : S → A → ℝ) (hπ : IsPolicy π)
    (μ : S → ℝ) (hμ : IsStateDist μ) :
    ∀ s : S, μ s / horizon γ ≤ futureStateDist P γ π μ s := by sorry

end SampleComplexityRL.CPI
