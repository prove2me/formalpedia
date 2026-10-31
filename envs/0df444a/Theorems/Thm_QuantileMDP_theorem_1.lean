-- Prove2me | Theorems.Thm_QuantileMDP_theorem_1
-- name    : QuantileMDP.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:09.198563+00:00
-- url     : https://prove2.me/theorems/226125c9-3308-4da5-926a-6a6857b86011
-- title:
--   Theorem 1 — $\tilde v_t(s,\tau,a)=\mathrm{OPT}(s,\tau,a,v_{t+1})$ (corrected: strict quantile budget in OPT)
-- statement:
--   Let $M$ be a model with finite state set $\mathcal S=\{s_1,\dots,s_n\}$ and finite action set, $T$ a horizon, $t<T$, $s$ a state, $a\in\mathcal A_t(s)$ an admissible action and $\tau\in[0,1]$. Let $v_{t+1}$ be the optimal value function (5) at time $t+1$ and $\tilde v_t$ the intermediate value function. Then
--
--   $$
--   \tilde v_t(s,\tau,a)=\mathrm{OPT}\bigl(s,\tau,a,v_{t+1}(\cdot,\cdot)\bigr)
--   =\sup_q\ \min_{i\in\{i\,:\,q_i\neq1\}}\bigl[v_{t+1}(s_i,q_i)+r_t(s,a,l_t(s,a,s_i))\bigr],
--   $$
--
--   the supremum being over $q\in[0,1]^n$ with $\sum_{i=1}^np_iq_i<\tau$ or $\sum_{i=1}^np_iq_i=0$, where $p_i=P(S_{t+1}=s_i\mid S_t=s,a_t=a)$. The supremum is attained by some such $q$, and the maximum defining $\tilde v_t(s,\tau,a)$ is attained by an admissible policy with $\mu_t(s)=a$.
--
--   Together with (6) this is the dynamic-programming step of the quantile MDP: the time-$t$ value function is computed from the time-$(t+1)$ value function as a function of both the state and the quantile level.
--
--   Differences from the source:
--   - correction: budget $\sum_ip_iq_i\le\tau$ → $\sum_ip_iq_i<\tau$ or $\sum_ip_iq_i=0$; reason: the printed statement is false — $\mathcal S=\{s_1,s_2\}$, one action, $T=1$, $t=0$, $P_0(s_1\mid s_1,a)=P_0(s_2\mid s_1,a)=1/2$, $r_0(s_1,a,s_1)=0$, $r_0(s_1,a,s_2)=10$, $\tau=1/2$: $q=(1,0)$ gives $10$, while the only policy's reward is $0$ or $10$ with probability $1/2$ each and $\tilde v_0(s_1,1/2,a)=0$.
--   - reading: "max$_a$" and the admissible actions → hypothesis $a\in\mathcal A_t(s)$; reason: for a non-admissible $a$ no policy has $\mu_t(s)=a$, and the paper's maximum ranges over admissible actions (p.8).
--   - generalization: admissible set $\mathcal A_t$ → $\mathcal A_t(s)$, depending on the state; reason: the paper's case is $\mathcal A_t(s)=\mathcal A_t$.
--   - encoding: $f_t$, $w_t$, $l_t$ of Assumption 1 → kernels $P_t(\cdot\mid s,a)$ and rewards $r_t(s,a,s')=r_t(s,a,l_t(s,a,s'))$; reason: every model of Assumption 1 induces such a pair with the same joint law, and every kernel model is one.
--   - encoding: policies on $H_t=(S_0,a_0,\dots,S_t)$ → deterministic functions of the state history; reason: for deterministic policies past actions are functions of past states.
--   - encoding: $\mathcal S=\{s_1,\dots,s_n\}$ and real values → the finite type $\mathcal S$ as index set, values in the extended reals; reason: same instances.
--   - encoding: the process from time $t$ → the model shifted by $t$, started at its time $0$, with a fresh policy; reason: the paper's histories $H'_k$ begin with $S_t$ (p.10).
--   - encoding: admissible sets $\mathcal A_t$ and the data $P_t,r_t$ for $t<T$ → nonempty sets and data for every $t\in\mathbb N$; reason: an empty $\mathcal A_t$ leaves no policy and the maximum undefined, and the data at $t\ge T$ is never used.
--   - encoding: the maxima over $q$ in OPT and over policies in $\tilde v_t$ → suprema in the extended reals together with clauses saying each is attained; reason: that is what the maxima assert.
-- source:
--   Li, Zhong, Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §3.2, Theorem 1 (8), p.11

import Mathlib
import Definitions.Def_QuantileMDP_quantile
import Definitions.Def_QuantileMDP_opt
import Definitions.Def_QuantileMDP_Model
import Definitions.Def_QuantileMDP_optValue

namespace QuantileMDP

/-- Theorem 1 (Value Function Dynamic Programming), corrected budget: for `t < T` and an
admissible action `a`, `ṽ_t(s, τ, a) = OPT(s, τ, a, v_{t+1}(·,·))`, where
`OPT = max_q min_{i : q_i ≠ 1} [v_{t+1}(s_i, q_i) + r_t(s, a, l_t(s, a, s_i))]` with
`p_i = P(S_{t+1} = s_i | S_t = s, a_t = a)` and `v_{t+1}` the optimal value function (5). Both
maxima are attained: the one over `q` in `OPT` and the one over policies in `ṽ_t`.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, §3.2, Theorem 1 (8),
p.11.

**Formalization Note** `OPT` is `opt` with the corrected budget `∑ p_i q_i < τ ∨ ∑ p_i q_i = 0`
(the printed `≤ τ` fails at `τ = 1/2` for one step to two equally likely states with rewards
`0` and `10`). The state space is indexed by the type `S` itself. The maximum over actions in the
paper ranges over admissible actions, so `a ∈ adm t s` is assumed. -/
theorem theorem_1 {S A : Type*} [Fintype S] [Fintype A] (M : Model S A) (T t : ℕ) (ht : t < T)
    (s : S) (a : A) (ha : a ∈ M.adm t s) (τ : ℝ) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    optValueAct M T t s τ a =
        opt (fun s' => (M.P t s a s').toReal)
          (fun s' q => optValue M T (t + 1) s' q + ((M.r t s a s' : ℝ) : EReal)) τ ∧
      OptAttained (fun s' => (M.P t s a s').toReal)
        (fun s' q => optValue M T (t + 1) s' q + ((M.r t s a s' : ℝ) : EReal)) τ ∧
      ∃ π : Policy S A, (M.shift t).Admissible π ∧ π 0 (fun _ => s) = a ∧
        quantile (rewardLaw (M.shift t) (T - t) π s) τ = optValueAct M T t s τ a := by sorry

end QuantileMDP
