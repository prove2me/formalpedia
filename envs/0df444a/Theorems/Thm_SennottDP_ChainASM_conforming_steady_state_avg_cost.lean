-- Prove2me | Theorems.Thm_SennottDP_ChainASM_conforming_steady_state_avg_cost
-- name    : SennottDP.ChainASM.conforming_steady_state_avg_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T14:51:45.936482+00:00
-- url     : https://prove2.me/theorems/bfd6b150-43de-41ba-84d9-973058d9ad90
-- title:
--   Proposition C.4.9 — a conforming AS has π_i(N) → π_i for all i and constant average costs J(N) → J_R
-- statement:
--   Let $\Gamma$ be a $z$ standard Markov chain with costs on a denumerable state space $S$, and let $(\Gamma_N)$ be a conforming approximating sequence. Let $R$ be the positive recurrent class of $\Gamma$ containing $z$ and $J_R$ its average cost. Then:
--
--   1. $\pi_i(N)\to\pi_i$ for all $i\in S$;
--   2. $J(N)\to J_R$, where $J(N)$ is the constant average cost on $\Gamma_N$ for $N\ge N^*$:
--   $$J(i)(N)=J(N)\ \text{ for } i\in S_N \text{ and } N \text{ large},\qquad \lim_{N\to\infty}J(N)=J_R.$$
--
--   Conformity thus delivers exactly what an approximation scheme is used for: the steady state distribution and the average cost of the finite chains converge to those of $\Gamma$.
--
--   **Formalization Note** The positive recurrent class containing $z$ is written as the communicating class of $z$ (for a $z$ standard chain it is positive recurrent, Proposition C.2.6). Part 2 is stated as the existence of a sequence $J(N)$ that equals $J(i)(N)$ for every $i\in S_N$ for all sufficiently large $N$ and converges to $J_R$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 307, Proposition C.4.9

import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain
import Definitions.Def_SennottDP_ChainASM_ApproxSeq
open scoped ENNReal NNReal
open Filter Topology
open Classical

namespace SennottDP.ChainASM

theorem conforming_steady_state_avg_cost {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (z : S) (hz : Γ.IsZStandard z) (AS : ApproxSeq Γ)
    (hconf : AS.IsConforming z) :
    (∀ i : S, Tendsto (fun N => AS.steadyStateN N i) atTop (𝓝 (Γ.steadyState i))) ∧
    ∃ Jc : ℕ → ℝ≥0∞, (∀ᶠ N in atTop, ∀ i ∈ AS.SN N, AS.avgCostN N i = Jc N) ∧
      Tendsto Jc atTop (𝓝 (Γ.classAvgCost (Γ.commClass z))) := by sorry

end SennottDP.ChainASM
