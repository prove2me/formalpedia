-- Prove2me | Theorems.Thm_ShockCBM_ControlLimit_display_10
-- name    : ShockCBM.ControlLimit.display_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:37.245077+00:00
-- url     : https://prove2.me/theorems/1ae815db-2e3c-4ff8-885c-6f202d3f0c86
-- title:
--   (10), p. 14 — value iteration converges and the value function V satisfies the Bellman optimality equation
-- statement:
--   Consider the collapsed MDP of the shock degradation model under its standing assumptions, with value iteration $V^0=0$, $V^{m+1}=\mathcal TV^m$ and $V(s)=\lim_m V^m(s)$. Then:
--   1. for every state $s$, the sequence $V^m(s)$ converges to $V(s)$;
--   2. $V$ satisfies the Bellman optimality equation (10): for $s=(x,n,t)$,
--   $$V(s)=\begin{cases}c_u+\gamma\,\mathbb E[V(s_0+A(s_0))], & x\ge\xi,\\ \min\{c_p+\gamma\,\mathbb E[V(s_0+A(s_0))],\ \gamma\,\mathbb E_s[V(s+A(s))]\}, & x<\xi;\end{cases}$$
--   3. $0\le V(s)\le c_u/(1-\gamma)$ for every $s$.
--
--   This is the analytic foundation for the structural results: the value function exists as a bounded fixed point of the Bellman operator, reached by value iteration from zero.
--
--   **Formalization Note** The paper asserts that $V$ satisfies (10) and that value iteration converges pointwise because the state space is countable, $\gamma\in(0,1)$ and costs are bounded (proof of Lemma 2, p. 32). The explicit bound $c_u/(1-\gamma)$ makes "costs are bounded" precise and guarantees that the expectations in (10) are genuine (summable) series.
-- source:
--   Drent, Drent, Arts, Kapodistria, Real-Time Integrated Learning and Decision Making for Cumulative Shock Degradation, Manufacturing & Service Operations Management 25(1) (2023), doi:10.1287/msom.2022.1149, accepted manuscript, §3.3, p. 14, (10); p. 32, (18) and proof of Lemma 2

import Mathlib
import Definitions.Def_ShockCBM_ControlLimit_NEF
import Definitions.Def_ShockCBM_ControlLimit_Setting

namespace ShockCBM.ControlLimit

theorem display_10 (M : Model) (hM : M.Standing) :
    (∀ s : State, Filter.Tendsto (fun m => M.valueIter m s) Filter.atTop (nhds (M.V s))) ∧
    (∀ s : State, M.V s = M.bellman M.V s) ∧
    (∀ s : State, 0 ≤ M.V s ∧ M.V s ≤ M.cu / (1 - M.γ)) := by sorry

end ShockCBM.ControlLimit
