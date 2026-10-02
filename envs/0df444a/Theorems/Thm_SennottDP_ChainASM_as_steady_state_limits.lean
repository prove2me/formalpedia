-- Prove2me | Theorems.Thm_SennottDP_ChainASM_as_steady_state_limits
-- name    : SennottDP.ChainASM.as_steady_state_limits
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-01T14:35:32.851835+00:00
-- url     : https://prove2.me/theorems/984e8333-7e77-4b78-83f0-951b9c337cb0
-- title:
--   Proposition C.4.3 — steady state probabilities along an AS: zero limits off positive recurrent states, subsequential limits bπ on a class
-- statement:
--   Let $(\Gamma_N)$ be an approximating sequence for the Markov chain $\Gamma$ on a denumerable state space $S$, and write $\pi_i(N)$ for the steady state probability of $i$ in $\Gamma_N$ (set to $0$ for $i\notin S_N$). Then:
--
--   1. If $i\in S$ is transient or null recurrent, then $\lim_{N\to\infty}\pi_i(N)=\pi_i=0$.
--   2. Let $R$ be a positive recurrent class of $\Gamma$. Given a sequence $N_r$, there exist a subsequence $N_s$ of $N_r$ and a constant $b$ with $0\le b\le 1$ such that
--   $$\lim_{s\to\infty}\pi_i(N_s)=b\,\pi_i,\qquad i\in R.$$
--
--   The constant $b$ measures how much of the steady state mass of the class $R$ survives the approximation; $b=1$ for all sequences is equivalent to $\pi_i(N)\to\pi_i$ on $R$.
--
--   **Formalization Note** "Transient or null recurrent" is encoded as "not positive recurrent", i.e. $m_{ii}=\infty$. The sequence $N_r$ is a strictly increasing sequence of indices and the subsequence is $N_s=N_{r(s)}$ for a strictly increasing $r(\cdot)$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 303, Proposition C.4.3

import Mathlib
import Definitions.Def_SennottDP_ChainASM_MarkovChain
import Definitions.Def_SennottDP_ChainASM_ApproxSeq
open scoped ENNReal NNReal
open Filter Topology
open Classical

namespace SennottDP.ChainASM

theorem as_steady_state_limits {S : Type*} [Countable S] [Infinite S]
    (Γ : MC S) (AS : ApproxSeq Γ) :
    (∀ i : S, ¬ Γ.PosRecurrent i →
      Tendsto (fun N => AS.steadyStateN N i) atTop (𝓝 (Γ.steadyState i)) ∧
        Γ.steadyState i = 0) ∧
    (∀ R : Set S, Γ.IsPosRecClass R → ∀ Nr : ℕ → ℕ, StrictMono Nr →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ b : ℝ≥0∞, b ≤ 1 ∧
        ∀ i ∈ R, Tendsto (fun s => AS.steadyStateN (Nr (φ s)) i) atTop
          (𝓝 (b * Γ.steadyState i))) := by sorry

end SennottDP.ChainASM
