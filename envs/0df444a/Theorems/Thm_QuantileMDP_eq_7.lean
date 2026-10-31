-- Prove2me | Theorems.Thm_QuantileMDP_eq_7
-- name    : QuantileMDP.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:01.18292+00:00
-- url     : https://prove2.me/theorems/c87be95f-6eef-476c-a10b-d6cd4c468698
-- title:
--   Equation (7) — the reward-to-go splits by the next state into a mixture of shifted continuation laws
-- statement:
--   Let $M$ be a model with finite state and action sets, $T$ a horizon, $t<T$, $s$ a state and $a$ an action. For an admissible policy $\pi_{t:T}$ started at time $t$ in state $s$ with first action $\mu_t(s)=a$, the law of the reward-to-go $\sum_{k=t}^{T-1}r_k(S_k,a_k,w_k)$ given $S_t=s$ is
--
--   $$
--   \mathcal L\Bigl[\sum_{k=t}^{T-1}r_k\ \Big|\ S_t=s\Bigr]=\sum_{s'\in\mathcal S}P_t(s'\mid s,a)\ \mathcal L\Bigl[r_t(s,a,s')+\sum_{k=t+1}^{T-1}r_k\ \Big|\ S_{t+1}=s'\Bigr],
--   $$
--
--   where the continuation after $S_{t+1}=s'$ follows the tail policy $\pi$ after the history $(s)$. Consequently, as in (7),
--
--   $$
--   \tilde v_t(s,\tau,a)=\max_{\{\pi_{t:T}\,:\,\mu_t(s)=a\}}Q_\tau\Bigl(\sum_{s'\in\mathcal S}\mathbf 1\{S_{t+1}=s'\mid S_t=s,a_t=a\}\Bigl[\sum_{k=t}^{T-1}r_k(S_k,a_k,w_k)\ \Big|\ S_t=s,S_{t+1}=s'\Bigr]\Bigr)
--   $$
--
--   for every $\tau$, the mixture inside $Q_\tau$ being the right-hand side of the first display.
--
--   This is the step that turns the time-$t$ problem into a quantile of a mixture over next states, to which Lemma 2 applies.
--
--   Differences from the source:
--   - generalization: (7), an identity of quantile maxima → the identity of laws (first conjunct) together with (7) (second conjunct); reason: applying $Q_\tau$ and the maximum to the identity of laws gives the printed (7).
--   - encoding: the sum of indicator-weighted conditional reward-to-go variables → the mixture $\sum_{s'}P_t(s'\mid s,a)\cdot$ (law of the continuation shifted by $r_t(s,a,s')$); reason: the law of that random variable.
--   - encoding: the process from time $t$ and the continuation from time $t+1$ → the models shifted by $t$ and $t+1$, the continuation policy being the policy's tail after $s$; reason: the paper's histories $H'_k$ begin with $S_t$ (p.10).
--   - encoding: the range of $t$ in the recursion ($t=T-1,\dots,0$) → hypothesis $t<T$; reason: same times.
--   - encoding: $f_t$, $w_t$, $l_t$ of Assumption 1 → kernels $P_t(\cdot\mid s,a)$ and rewards $r_t(s,a,s')=r_t(s,a,l_t(s,a,s'))$; reason: every model of Assumption 1 induces such a pair with the same joint law, and every kernel model is one.
--   - encoding: policies on $H_t=(S_0,a_0,\dots,S_t)$ → deterministic functions of the state history; reason: for deterministic policies past actions are functions of past states.
--   - generalization: admissible set $\mathcal A_t$ → $\mathcal A_t(s)$, depending on the state; reason: the paper's case is $\mathcal A_t(s)=\mathcal A_t$.
--   - encoding: admissible sets $\mathcal A_t$ and the data $P_t,r_t$ for $t<T$ → nonempty sets and data for every $t\in\mathbb N$; reason: an empty $\mathcal A_t$ leaves no policy and the maximum undefined, and the data at $t\ge T$ is never used.
-- source:
--   Li, Zhong, Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §3.2, (7), p.10, and the display following it, p.11

import Mathlib
import Definitions.Def_QuantileMDP_quantile
import Definitions.Def_QuantileMDP_Model
import Definitions.Def_QuantileMDP_optValue

open MeasureTheory

namespace QuantileMDP

/-- Equation (7): conditioning on the next state. For `t < T`, a policy started at time `t` in
state `s` whose first action is `a` has reward-to-go law
`∑_{s'} P_t(s' | s, a) · Law(r_t(s, a, s') + ∑_{k=t+1}^{T-1} r_k | S_{t+1} = s')`, the continuation
being the policy's tail after `s`; hence `ṽ_t(s, τ, a)` is the maximum of `Q_τ` of this mixture.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, §3.2, (7), p.10
(and the display following it, p.11).

**Formalization Note** The first conjunct is the identity of laws behind (7); the second is (7)
at the level of quantiles. The time-`t` process is `M.shift t`, and the process after
`S_{t+1} = s'` is `M.shift (t+1)` under the policy `π.tail s`. -/
theorem eq_7 {S A : Type*} [Fintype S] [Fintype A] (M : Model S A) (T t : ℕ) (ht : t < T) (s : S)
    (a : A) :
    (∀ π : Policy S A, (M.shift t).Admissible π → π 0 (fun _ => s) = a →
      rewardLaw (M.shift t) (T - t) π s =
        ∑ s' : S, M.P t s a s' •
          (rewardLaw (M.shift (t + 1)) (T - (t + 1)) (π.tail s) s').map
            (fun x => x + M.r t s a s')) ∧
    (∀ τ : ℝ, optValueAct M T t s τ a =
      ⨆ (π : Policy S A) (_ : (M.shift t).Admissible π) (_ : π 0 (fun _ => s) = a),
        quantile (∑ s' : S, M.P t s a s' •
          (rewardLaw (M.shift (t + 1)) (T - (t + 1)) (π.tail s) s').map
            (fun x => x + M.r t s a s')) τ) := by sorry

end QuantileMDP
