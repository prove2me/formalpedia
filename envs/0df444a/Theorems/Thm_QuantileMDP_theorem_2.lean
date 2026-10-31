-- Prove2me | Theorems.Thm_QuantileMDP_theorem_2
-- name    : QuantileMDP.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:42:54.941172+00:00
-- url     : https://prove2.me/theorems/a7925b2e-33ca-4a12-85e9-752576a3e32b
-- title:
--   Theorem 2 — backward DP computes $v_0(s,\tau)=\max_\pi Q^\pi_\tau[\sum_{k<T}r_k]$ (corrected: strict quantile budget in OPT)
-- statement:
--   Let $M$ be a finite-horizon Markov decision process with finite state set $\mathcal S$, finite action set $\mathcal A$, non-stationary transition laws $P_t(\cdot\mid s,a)$, rewards $r_t(s,a,s')$ and nonempty admissible action sets. Let $T\in\mathbb N$ be a horizon. Put $v_T(s,\tau)=0$ for all $s\in\mathcal S$ and $\tau\in[0,1]$, and compute iteratively, for $t=T-1,\dots,0$,
--
--   $$
--   v_t(s,\tau)=\max_a\ \mathrm{OPT}\bigl(s,\tau,a,v_{t+1}(\cdot,\cdot)\bigr),
--   $$
--
--   with $\mathrm{OPT}$ the problem (8) with the budget $\sum_ip_iq_i<\tau$ or $\sum_ip_iq_i=0$. Then for every start state $s$ and every $\tau\in[0,1]$,
--
--   $$
--   v_0(s,\tau)=\max_{\pi\in\Pi}Q^\pi_\tau\Bigl[\sum_{k=0}^{T-1}r_k(S_k,a_k,w_k)\Bigr],
--   $$
--
--   where $\Pi$ is the set of all admissible deterministic history-dependent policies and the quantile is that of the cumulative reward from $S_0=s$; the maximum is attained.
--
--   This is the main result of the paper: the quantile-optimal value of a finite-horizon MDP is computed by a backward dynamic program over the pair (state, quantile level), even though the optimal policy itself is in general history dependent.
--
--   Differences from the source:
--   - correction: budget $\sum_ip_iq_i\le\tau$ in OPT → $\sum_ip_iq_i<\tau$ or $\sum_ip_iq_i=0$; reason: the printed statement is false — $\mathcal S=\{s_1,s_2\}$, one action, $T=1$, $P_0(s_1\mid s_1,a)=P_0(s_2\mid s_1,a)=1/2$, $r_0(s_1,a,s_1)=0$, $r_0(s_1,a,s_2)=10$ (Assumption 1 holds with $W=\mathcal S$, $f_0(s,a,w)=w$, $l_0(s,a,s')=s'$), $\tau=1/2$: the printed recursion gives $v_0(s_1,1/2)=10$ via $q=(1,0)$, while the only policy's reward is $0$ or $10$ with probability $1/2$ each, whose $1/2$-quantile is $0$.
--   - encoding: $f_t$, $w_t$, $l_t$ of Assumption 1 → kernels $P_t(\cdot\mid s,a)$ and rewards $r_t(s,a,s')=r_t(s,a,l_t(s,a,s'))$; reason: every model of Assumption 1 induces such a pair with the same joint law of states, actions and rewards, and every kernel model is one ($W=\mathcal S$, $f_t(s,a,w)=w$, $l_t(s,a,s')=s'$).
--   - encoding: policies on $H_t=(S_0,a_0,\dots,S_t)$ → deterministic functions of the state history; reason: for deterministic policies past actions are functions of past states.
--   - generalization: admissible set $\mathcal A_t$ → $\mathcal A_t(s)$, depending on the state; reason: the paper's case is $\mathcal A_t(s)=\mathcal A_t$.
--   - encoding: $Q_0=\inf\{X\}$, $Q_1=\sup\{X\}$ → the essential infimum and supremum of footnote 1, valued in the extended reals; reason: footnote 1 gives the precise form.
--   - encoding: the law of $\sum_{k<T}r_k$ given $S_0=s$ → a finite sum of Dirac masses over state paths from $s$ weighted by their probabilities; reason: it is that law.
--   - encoding: "$\max_{\pi\in\Pi}$" → the value is the greatest element of the set of quantiles attained by admissible policies; reason: that is what the maximum asserts.
--   - encoding: admissible sets $\mathcal A_t$ and the data $P_t,r_t$ for $t<T$ → nonempty sets and data for every $t\in\mathbb N$; reason: an empty $\mathcal A_t$ leaves no policy and the maximum undefined, and the data at $t\ge T$ is never used.
--   - encoding: the maxima over $a$ and $q$ in the recursion → suprema in the extended reals in the definition of the recursion; reason: same values: only the value of each step enters the recursion.
-- source:
--   Li, Zhong, Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §3.3, Theorem 2, p.12

import Mathlib
import Definitions.Def_QuantileMDP_quantile
import Definitions.Def_QuantileMDP_Model
import Definitions.Def_QuantileMDP_dpValue

namespace QuantileMDP

/-- Theorem 2 (Optimal Value Function), corrected budget: let `v_T(s, τ) = 0` and compute
`v_t(s, τ) = max_a OPT(s, τ, a, v_{t+1}(·,·))` for `t = T-1, …, 0`. Then `v_0(s, τ)` is the maximum,
over all admissible history-dependent policies `π`, of `Q^π_τ[∑_{k=0}^{T-1} r_k(S_k, a_k, w_k)]`
from `S_0 = s`, for every `τ ∈ [0,1]`.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, §3.3, Theorem 2,
p.12.

**Formalization Note** `OPT` is `opt` with the corrected budget `∑ p_i q_i < τ ∨ ∑ p_i q_i = 0`
(the printed `≤ τ` gives `10` instead of `0` at `τ = 1/2` for one step to two equally likely
states with rewards `0` and `10`). "max" is `IsGreatest`: the value is attained by an admissible
policy and no admissible policy does better. Every horizon `T` (including `0`) and every
`τ ∈ [0,1]`, endpoints included. -/
theorem theorem_2 {S A : Type*} [Fintype S] [Fintype A] (M : Model S A) (T : ℕ) (s : S) (τ : ℝ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    IsGreatest {x : EReal | ∃ π : Policy S A, M.Admissible π ∧
        x = quantile (rewardLaw M T π s) τ} (dpValue M T 0 s τ) := by sorry

end QuantileMDP
