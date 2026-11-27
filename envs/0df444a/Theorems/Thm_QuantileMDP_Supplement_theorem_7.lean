-- Prove2me | Theorems.Thm_QuantileMDP_Supplement_theorem_7
-- name    : QuantileMDP.Supplement.theorem_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T02:54:38.113056+00:00
-- url     : https://prove2.me/theorems/0bb721c5-d9df-5c9e-be8d-2b96e9cd0c1c
-- title:
--   Theorem 7 (Infinite-Horizon Optimal Policy) — the stationary augmented-state policy attains $v(s_0,\tau_0)$ (corrected: strict quantile budget in OPT)
-- statement:
--   Let $M$ be a stationary Markov decision process with finite state set $\mathcal S=\{s_1,\dots,s_n\}$, finite action set $\mathcal A$, transition law $P(\cdot\mid s,a)$, reward $r(s,a,s')$ and nonempty admissible action sets $\mathcal A(s)$, and let $\gamma\in(0,1)$. Let $v$ be the optimal value function (13),
--   $$
--   v(s,\tau)=\max_{\pi\in\Pi}Q^\pi_\tau\Bigl[\sum_{t=0}^\infty\gamma^tr(S_t,a_t,w_t)\Bigm|S_0=s\Bigr],
--   $$
--   over all admissible history-dependent policies, and let $\tilde v(s,\tau,a)=\mathrm{OPT}(s,\tau,a,\gamma v(\cdot,\cdot))$, that is
--   $$
--   \tilde v(s,\tau,a)=\sup_q\ \min_{i:\,q_i\ne1}\bigl[\gamma\,v(s_i,q_i)+r(s,a,s_i)\bigr]
--   $$
--   over $q\in[0,1]^n$ with $\sum_ip_iq_i<\tau$ or $\sum_ip_iq_i=0$, $p_i=P(s_i\mid s,a)$.
--
--   Fix any choice of
--
--   1. actions $\mu(s,\tau)\in\mathcal A(s)$ with $\mu(s,\tau)\in\arg\max_a\tilde v(s,\tau,a)$ for $\tau\in[0,1]$;
--   2. vectors $q^*(s,\tau)$ that solve $\mathrm{OPT}\bigl(s,\tau,\mu(s,\tau),\gamma v\bigr)$ (feasible and attaining the supremum) at every pair $(S_t,\tau_t)$ that the process started at $(s_0,\tau_0)$ reaches with positive probability.
--
--   Start in $s_0$ with $\tau_0\in[0,1]$, play $a_t=\mu(S_t,\tau_t)$ and, once $S_{t+1}=s_i$ is observed, set $\tau_{t+1}=q^*(S_t,\tau_t)_i$. Then the policy $\pi^*=\{\mu_t\}_{t\ge0}$ so obtained is admissible, it is optimal for the objective (13), and it obtains the optimal value:
--   $$
--   Q^{\pi^*}_{\tau_0}\Bigl[\sum_{t=0}^\infty\gamma^tr(S_t,a_t,w_t)\Bigm|S_0=s_0\Bigr]=v(s_0,\tau_0).
--   $$
--
--   As in the finite-horizon case (Theorem 3), the infinite-horizon quantile objective is optimized by a policy on the state augmented with one quantile level, now with stationary decision and update rules.
--
--   **Formalization Note** $v$ is `infiniteValue M γ` and the policy is `augmentedPolicy` with time-independent maps. Stationarity is $P_k=P_0$, $r_k=r_0$ and $\mathcal A_k=\mathcal A_0$ for all $k$. The page says "let $q^*$ be the solution" of OPT at the state and level reached at time $t$; such a solution need not exist (two states, uniform transitions, reward $1$ on entering the second state, $\gamma=1/2$, $\tau=1/2$: the supremum $1$ of OPT is not attained), so its existence is a hypothesis on the selection, required exactly at the pairs $(S_t,\tau_t)$ reached with positive probability from $(s_0,\tau_0)$ (state histories starting at $s_0$ with positive path weight), and is not asserted. The action map is admissible at every level and maximizes $\tilde v$ at every level in $[0,1]$ (an admissible maximizer always exists, $\mathcal A$ being finite).
--
--   Differences from the source:
--   - correction: budget $\sum_ip_iq_i\le\tau$ in OPT → $\sum_ip_iq_i<\tau$ or $\sum_ip_iq_i=0$; reason: the printed statement is false — states $s_0,s_1,s_2,s_3$, $s_1,s_2\to s_3$ and $s_3\to s_3$ with reward $0$ under both actions; at $s_0$ action $a$ moves to $s_1$ or $s_2$ with probability $1/2$ each, with rewards $0$ and $10$, and action $b$ moves to $s_3$ with reward $5$ (reward $5$ for every next state under $b$); any $\gamma\in(0,1)$, $\tau_0=1/2$. Then $v(s_0,1/2)=5$ (play $b$), but $q$ with $q_{s_2}=0$ and all other coordinates $1$ satisfies the printed budget for $a$ and gives $\tilde v(s_0,1/2,a)\ge10>5=\tilde v(s_0,1/2,b)$, so the printed rule plays $a$, whose $1/2$-quantile is $0<5$.
--   - reading: "Let $q^*$ be the solution to OPT$(S_t,\mu_t(S_t,\tau_t),\tau_t,\gamma v)$" → hypothesis that at every pair $(S_t,\tau_t)$ reached with positive probability the selected $q^*$ is feasible and attains OPT; reason: the page presumes a solution exists, which can fail (counterexample in the Formalization Note); the theorem is stated for every selection, with the solution property required only where the page uses it.
--   - encoding: stationary reward of §5.3 → $P_k=P_0$, $r_k=r_0$, $\mathcal A_k=\mathcal A_0$; reason: §5.3 takes $r_t=r$ stationary and the value iteration and $\tilde v$ carry no time index, so the model is stationary.
--   - encoding: $\mu$ is defined at the levels that occur → the action map is admissible for all $s,\tau$ and an argmax of $\tilde v$ for all $\tau\in[0,1]$; reason: an admissible argmax exists at every level ($\mathcal A$ finite, admissible sets nonempty), so every page selection extends; values elsewhere do not affect the reward.
-- source:
--   Li, Zhong, Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §5.3, Theorem 7, pp.23–24; (13), p.23

import Mathlib
import Definitions.Def_QuantileMDP_quantile
import Definitions.Def_QuantileMDP_Model
import Definitions.Def_QuantileMDP_opt
import Definitions.Def_QuantileMDP_augmentedPolicy
import Definitions.Def_QuantileMDP_discountedPath
import Definitions.Def_QuantileMDP_trajectory
import Definitions.Def_QuantileMDP_Supplement_infiniteValue

open MeasureTheory

namespace QuantileMDP.Supplement

/-- Theorem 7 (Infinite-Horizon Optimal Policy), corrected budget. Let `v` be the optimal value
function (13) and `ṽ(s, τ, a) = OPT(s, τ, a, γ v(·,·))`. Augment the state with a quantile level:
start at `τ_0 = τ`, play `μ_t(S_t, τ_t) = act S_t τ_t`, an `argmax_a ṽ(S_t, τ_t, a)` over the
admissible actions, and after reaching `S_{t+1} = s_i` set `τ_{t+1} = q*_i`, where
`q* = next S_t τ_t` is a solution of `OPT(S_t, μ_t(S_t, τ_t), τ_t, γ v(·,·))`. For every such
choice, the policy `π = {μ_t}` is admissible, optimal for the objective (13), and obtains
`v(s_0, τ_0)`.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, §5.3, Theorem 7,
pp.23–24.

**Formalization Note** The model is stationary (§5.3: `r_t = r(S_t, a_t, w_t)` and the value
iteration carry no time index): `M.P k = M.P 0`, `M.r k = M.r 0`, `M.adm k = M.adm 0`; `γ ∈ (0,1)`.
`v = infiniteValue M γ`, the supremum (13) over all admissible history-dependent policies.
`OPT(s, τ, a, γ v)` is `opt` with `p_i = P(s_i | s, a)`, `g_i(q) = γ v(s_i, q) + r(s, a, s_i)` (the
immediate reward is part of OPT, (8)) and the corrected budget `∑ p_i q_i < τ ∨ ∑ p_i q_i = 0`.
"Let `q*` be the solution to OPT(S_t, μ_t(S_t, τ_t), τ_t, γ v)" is a hypothesis on the selection
`next` at the pairs `(S_t, τ_t)` the process reaches: for every state history `h = (S_0, …, S_t)`
with `S_0 = s₀` and positive probability under the policy, `next S_t τ_t` is feasible and attains
`opt`, where `τ_t = policyLevel … t 0 τ₀ h` is the level the policy carries. A maximizer of OPT need
not exist at every level (two states, uniform transitions, reward `1` on entering the second state,
`γ = 1/2`, `τ = 1/2`: the supremum `1` of `OPT` is not attained), so its existence is neither
asserted nor required at levels the process does not reach. The action map is admissible
everywhere and maximizes `ṽ` at every level in `[0,1]` (an admissible maximizer always exists: `A`
is finite and `adm` nonempty). The maps do not depend on time; the policy is `augmentedPolicy`
with the constant maps. Every start state `s₀` and every `τ₀ ∈ [0,1]`. -/
theorem theorem_7 {S A : Type*} [Fintype S] [Fintype A] [MeasurableSpace S]
    [MeasurableSingletonClass S] (M : Model S A)
    (hP : ∀ k, M.P k = M.P 0) (hr : ∀ k, M.r k = M.r 0) (ha : ∀ k, M.adm k = M.adm 0)
    (γ : ℝ) (hγ₀ : 0 < γ) (hγ₁ : γ < 1)
    (act : S → ℝ → A) (next : S → ℝ → S → ℝ)
    (hadm : ∀ s τ, act s τ ∈ M.adm 0 s)
    (hmax : ∀ s τ, τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a ∈ M.adm 0 s,
      opt (fun i => (M.P 0 s a i).toReal)
          (fun i q => (γ : EReal) * infiniteValue M γ i q + ((M.r 0 s a i : ℝ) : EReal)) τ ≤
        opt (fun i => (M.P 0 s (act s τ) i).toReal)
          (fun i q => (γ : EReal) * infiniteValue M γ i q + ((M.r 0 s (act s τ) i : ℝ) : EReal)) τ)
    (s₀ : S) (τ₀ : ℝ) (hτ₀ : τ₀ ∈ Set.Icc (0 : ℝ) 1)
    (hsol : ∀ (t : ℕ) (h : Fin (t + 1) → S), h 0 = s₀ →
      pathWeight M (augmentedPolicy (fun _ => act) (fun _ => next) 0 τ₀) h ≠ 0 →
      let s := h (Fin.last t)
      let τ := policyLevel (fun _ => next) t 0 τ₀ h
      next s τ ∈ Feasible (fun i => (M.P 0 s (act s τ) i).toReal) τ ∧
        (⨅ i, ⨅ (_ : next s τ i ≠ 1),
            ((γ : EReal) * infiniteValue M γ i (next s τ i) +
              ((M.r 0 s (act s τ) i : ℝ) : EReal))) =
          opt (fun i => (M.P 0 s (act s τ) i).toReal)
            (fun i q => (γ : EReal) * infiniteValue M γ i q +
              ((M.r 0 s (act s τ) i : ℝ) : EReal)) τ) :
    let π₀ : Policy S A := augmentedPolicy (fun _ => act) (fun _ => next) 0 τ₀
    let Q : Policy S A → EReal := fun π =>
      quantile ((trajectoryLaw M π s₀).map (fun w => ∑' k, γ ^ k * stepReward M π k w)) τ₀
    M.Admissible π₀ ∧ (∀ π : Policy S A, M.Admissible π → Q π ≤ Q π₀) ∧
      Q π₀ = infiniteValue M γ s₀ τ₀ := by sorry

end QuantileMDP.Supplement
