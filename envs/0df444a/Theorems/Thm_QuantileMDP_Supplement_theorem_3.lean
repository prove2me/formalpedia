-- Prove2me | Theorems.Thm_QuantileMDP_Supplement_theorem_3
-- name    : QuantileMDP.Supplement.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:53:42.30443+00:00
-- url     : https://prove2.me/theorems/05ec93f8-c78c-40fc-b8aa-809897fc680e
-- title:
--   Theorem 3 (Optimal Policy) — the augmented-state policy built from any argmax of $\tilde v_t$ and any OPT solution attains $v_0(s_0,\tau_0)$ (corrected: strict quantile budget in OPT)
-- statement:
--   Let $M$ be a finite-horizon Markov decision process with finite state set $\mathcal S=\{s_1,\dots,s_n\}$, finite action set $\mathcal A$, non-stationary transition laws $P_t(\cdot\mid s,a)$, rewards $r_t(s,a,s')$ and nonempty admissible action sets $\mathcal A_t(s)$, and let $T\in\mathbb N$ be the horizon. Let $v_t$ be the value function computed by the backward recursion of Theorem 2 ($v_T=0$, $v_t(s,\tau)=\max_a\mathrm{OPT}(s,\tau,a,v_{t+1})$), and let $\tilde v_t(s,\tau,a)$ be the intermediate value function of §3.2 (the best $\tau$-quantile of the reward from time $t$ in state $s$ when the first action is $a$). Here
--   $$
--   \mathrm{OPT}(s,\tau,a,w)=\max_{q}\ \min_{i:\,q_i\neq1}\bigl[w(s_i,q_i)+r_t(s,a,s_i)\bigr]
--   $$
--   over $q\in[0,1]^n$ with $\sum_ip_iq_i<\tau$ or $\sum_ip_iq_i=0$, where $p_i=P_t(s_i\mid s,a)$.
--
--   The policy augments the state with a quantile level. Fix any choice of
--
--   1. actions $\mu_t(s,\tau)\in\mathcal A_t(s)$ with $\mu_t(s,\tau)\in\arg\max_a\tilde v_t(s,\tau,a)$ for $t<T$ and $\tau\in[0,1]$;
--   2. vectors $q^*_t(s,\tau)$ that solve $\mathrm{OPT}\bigl(s,\tau,\mu_t(s,\tau),v_{t+1}\bigr)$ (feasible and attaining the maximum) for $t<T$ and $\tau\in[0,1]$.
--
--   Start in $s_0$ with $\tau_0\in[0,1]$, play $a_t=\mu_t(S_t,\tau_t)$ and, once $S_{t+1}=s_i$ is observed, set $\tau_{t+1}=q^*_t(S_t,\tau_t)_i$. Then this history-dependent policy $\pi^*$ is admissible, it is optimal for the objective (3),
--   $$
--   Q_{\tau_0}^{\pi}\Bigl[\sum_{k=0}^{T-1}r_k\Bigr]\le Q_{\tau_0}^{\pi^*}\Bigl[\sum_{k=0}^{T-1}r_k\Bigr]\quad\text{for every admissible }\pi,
--   $$
--   and it obtains the optimal value: $Q_{\tau_0}^{\pi^*}\bigl[\sum_{k=0}^{T-1}r_k\bigr]=v_0(s_0,\tau_0)$, the quantiles being those of the cumulative reward from $S_0=s_0$.
--
--   The quantile level $\tau_t$ summarizes the history: an optimal policy for the quantile objective can be executed with the current state and one real number, and any maximizing action and any solution of OPT may be used.
--
--   **Formalization Note** $\tilde v_t$ is `optValueAct` and $v_{t+1}$ is `dpValue M T (t+1)`; the policy is `augmentedPolicy act next 0 τ₀`. The maximizing and solution properties are assumed for $t<T$ and $\tau\in[0,1]$, the times and levels that occur; the action map is assumed admissible at every time and level so that the induced policy is admissible at every time (any choice on $t<T$, $\tau\in[0,1]$ extends to one). Every horizon $T$, including $T=0$, and every $\tau_0\in[0,1]$.
--
--   Differences from the source:
--   - correction: budget $\sum_ip_iq_i\le\tau$ in OPT → $\sum_ip_iq_i<\tau$ or $\sum_ip_iq_i=0$; reason: the printed statement is false — $\mathcal S=\{s_1,s_2\}$, one action, $T=1$, $P_0(s_1\mid s_1,a)=P_0(s_2\mid s_1,a)=1/2$, $r_0(s_1,a,s_1)=0$, $r_0(s_1,a,s_2)=10$, $\tau_0=1/2$: $q^*=(1,0)$ solves the printed OPT with value $10$, so the policy would obtain $10$, but every policy has $1/2$-quantile $0$.
--   - encoding: the action map is defined for all times and levels and admissible everywhere → hypothesis `act t s τ ∈ M.adm t s` for all $t,s,\tau$; reason: the page defines $\mu_t$ only on the times and levels that occur; every such choice extends admissibly, and the values elsewhere do not affect the reward.
-- source:
--   Li, Zhong, Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §3.3, Theorem 3, pp.13–14

import Mathlib
import Definitions.Def_QuantileMDP_quantile
import Definitions.Def_QuantileMDP_Model
import Definitions.Def_QuantileMDP_opt
import Definitions.Def_QuantileMDP_dpValue
import Definitions.Def_QuantileMDP_optValue
import Definitions.Def_QuantileMDP_augmentedPolicy

namespace QuantileMDP.Supplement

/-- Theorem 3 (Optimal Policy), corrected budget. Augment the state with a quantile level: start
at `τ_0 = τ`, play `μ_t(S_t, τ_t) = act t S_t τ_t`, an `argmax_a ṽ_t(S_t, τ_t, a)` over the
admissible actions, and after reaching `S_{t+1} = s_i` set `τ_{t+1} = q*_i`, where
`q* = next t S_t τ_t` is a solution of `OPT(S_t, μ_t(S_t, τ_t), τ_t, v_{t+1}(·,·))` with `v_{t+1}`
computed as in Theorem 2. For **every** such choice of maximizing actions and of OPT solutions,
the resulting policy is admissible, optimal for the objective (3), and obtains `v_0(s_0, τ_0)`.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, §3.3, Theorem 3,
pp.13–14.

**Formalization Note** `ṽ_t(s, τ, a)` is `optValueAct M T t s τ a` (§3.2), `v_{t+1}` is
`dpValue M T (t + 1)` (the recursion of Theorem 2), and `OPT(s, τ, a, w)` is `opt` with
`p_i = P_t(s_i | s, a)`, `g_i(q) = w(s_i, q) + r_t(s, a, s_i)` and the corrected budget
`∑ p_i q_i < τ ∨ ∑ p_i q_i = 0` (the printed `≤ τ` makes the statement false). "`q*` is the
solution" is: `q*` is feasible and its objective equals the optimal value `opt`. The maximizing
and solution properties are required for `t < T` and `τ ∈ [0,1]`, where the page uses them; the
action map is required admissible everywhere so that the induced history-dependent policy
(`augmentedPolicy act next 0 τ₀`) is admissible at every time. Every horizon `T` (including `0`)
and every `τ₀ ∈ [0,1]`. -/
theorem theorem_3 {S A : Type*} [Fintype S] [Fintype A] (M : Model S A) (T : ℕ)
    (act : ℕ → S → ℝ → A) (next : ℕ → S → ℝ → S → ℝ)
    (hadm : ∀ t s τ, act t s τ ∈ M.adm t s)
    (hmax : ∀ t < T, ∀ s τ, τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a ∈ M.adm t s,
      optValueAct M T t s τ a ≤ optValueAct M T t s τ (act t s τ))
    (hsol : ∀ t < T, ∀ s τ, τ ∈ Set.Icc (0 : ℝ) 1 →
      next t s τ ∈ Feasible (fun i => (M.P t s (act t s τ) i).toReal) τ ∧
        (⨅ i, ⨅ (_ : next t s τ i ≠ 1),
            (dpValue M T (t + 1) i (next t s τ i) + ((M.r t s (act t s τ) i : ℝ) : EReal))) =
          opt (fun i => (M.P t s (act t s τ) i).toReal)
            (fun i q => dpValue M T (t + 1) i q + ((M.r t s (act t s τ) i : ℝ) : EReal)) τ)
    (s₀ : S) (τ₀ : ℝ) (hτ₀ : τ₀ ∈ Set.Icc (0 : ℝ) 1) :
    M.Admissible (augmentedPolicy act next 0 τ₀) ∧
      (∀ π : Policy S A, M.Admissible π →
        quantile (rewardLaw M T π s₀) τ₀ ≤
          quantile (rewardLaw M T (augmentedPolicy act next 0 τ₀) s₀) τ₀) ∧
      quantile (rewardLaw M T (augmentedPolicy act next 0 τ₀) s₀) τ₀ = dpValue M T 0 s₀ τ₀ := by sorry

end QuantileMDP.Supplement
