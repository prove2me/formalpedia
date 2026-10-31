-- Prove2me | Theorems.Thm_QuantileMDP_eq_6
-- name    : QuantileMDP.eq_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:14.810827+00:00
-- url     : https://prove2.me/theorems/71382951-b8d8-484a-afe0-77af5d26b7ea
-- title:
--   Equation (6) — $v_t(s,\tau)=\max_a\tilde v_t(s,\tau,a)$
-- statement:
--   Let $M$ be a model with finite state and action sets, $T$ a horizon, $t$ a time, $s$ a state and $\tau$ a level. Then the optimal value function (5) is the maximum of the intermediate value function over the admissible first actions:
--
--   $$
--   v_t(s,\tau)=\max_{a\in\mathcal A_t(s)}\tilde v_t(s,\tau,a),
--   $$
--
--   the maximum being attained by an admissible action.
--
--   This is the step that, combined with Theorem 1, gives the backward recursion of Theorem 2.
--
--   Differences from the source:
--   - generalization: $t\in\{0,\dots,T-1\}$, $\tau\in[0,1]$ → every $t$ and every $\tau$; reason: the statement is true as stated for all of them and specializes to the page's range.
--   - generalization: admissible set $\mathcal A_t$ → $\mathcal A_t(s)$, depending on the state; reason: the paper's case is $\mathcal A_t(s)=\mathcal A_t$.
--   - encoding: max over $a$ → supremum over $a\in\mathcal A_t(s)$ in the extended reals, with a clause that some admissible $a$ attains it; reason: the first action of an admissible policy is admissible (p.8), and the clause is what the maximum asserts.
--   - encoding: $f_t$, $w_t$, $l_t$ of Assumption 1 → kernels $P_t(\cdot\mid s,a)$ and rewards $r_t(s,a,s')=r_t(s,a,l_t(s,a,s'))$; reason: every model of Assumption 1 induces such a pair with the same joint law, and every kernel model is one.
--   - encoding: policies on $H_t=(S_0,a_0,\dots,S_t)$ → deterministic functions of the state history; reason: for deterministic policies past actions are functions of past states.
--   - encoding: the process from time $t$ → the model shifted by $t$, started at its time $0$, with a fresh policy; reason: the paper's histories $H'_k$ begin with $S_t$ (p.10).
--   - encoding: admissible sets $\mathcal A_t$ and the data $P_t,r_t$ for $t<T$ → nonempty sets and data for every $t\in\mathbb N$; reason: an empty $\mathcal A_t$ leaves no policy and the maximum undefined, and the data at $t\ge T$ is never used.
-- source:
--   Li, Zhong, Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §3.2, (6), p.10

import Mathlib
import Definitions.Def_QuantileMDP_Model
import Definitions.Def_QuantileMDP_optValue

namespace QuantileMDP

/-- Equation (6): `v_t(s, τ) = max_a ṽ_t(s, τ, a)`, the maximum over admissible actions, which is
attained.
Li, Zhong, Brandeau, *Quantile Markov Decision Processes*, arXiv:1711.05788v5, §3.2, (6), p.10.

**Formalization Note** Stated for every `t` (for `t ≥ T` both sides are the quantile of the
point mass at `0`) and every `τ`. -/
theorem eq_6 {S A : Type*} [Fintype S] [Fintype A] (M : Model S A) (T t : ℕ) (s : S) (τ : ℝ) :
    optValue M T t s τ = (⨆ a ∈ M.adm t s, optValueAct M T t s τ a) ∧
      ∃ a ∈ M.adm t s, optValueAct M T t s τ a = optValue M T t s τ := by sorry

end QuantileMDP
