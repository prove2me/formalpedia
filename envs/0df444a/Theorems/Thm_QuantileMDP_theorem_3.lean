-- Prove2me | Theorems.Thm_QuantileMDP_theorem_3
-- name    : QuantileMDP.theorem_3
-- status  : Proved
-- author  : @shuffle
-- created : 2026-11-14T01:39:31.381421+00:00
-- url     : https://prove2.me/theorems/45fc2d8a-6c2f-4b86-8ddc-6afa51353431
-- title:
--   Quantile MDP Theorem 3 — forward execution on the augmented state attains the backward value
-- statement:
--   For a finite MDP and horizon $T$, there are action and level-update maps $a_t(s,u)$ and $q_t(s,u)(s')$. At each $t<T$ and $u\in[0,1]$, the action is admissible and maximizes the fixed-action backward value. The allocation attains that fixed-action value:
--   $$
--   \min_{i:q_i\ne 1}\bigl[v_{t+1}(i,q_i)+r_t(s,a_t(s,u),i)\bigr]
--   =\mathrm{OPT}(s,u,a_t(s,u),v_{t+1})=v_t(s,u).
--   $$
--   Here $v_t$ is computed by the backward recursion. With $p_i=P_t(i\mid s,a_t(s,u))$, feasibility means $q_i\in[0,1]$ and $\sum_i p_iq_i<u$ or $\sum_i p_iq_i=0$.
--
--   Starting at any time $t$ and initial quantile level $u$, at each step use $a_k(S_k,u_k)$ and set $u_{k+1}=q_k(S_k,u_k)(S_{k+1})$ after observing the next state. The induced history-dependent policy is admissible and attains the backward value $v_t(s,u)$ for the cumulative reward from $s$. The time-zero case is Theorem 3 of Li, Zhong and Brandeau. The statement uses the corrected budget of the existing finite-horizon formalization, including levels zero and one.
-- source:
--   Li, Zhong and Brandeau, Quantile Markov Decision Processes, arXiv:1711.05788v5, §3.3, Theorem 3, pp. 13–14. https://arxiv.org/abs/1711.05788v5

import Definitions.Def_QuantileMDP_augmentedPolicy
import Definitions.Def_QuantileMDP_dpValue
import Definitions.Def_QuantileMDP_quantile

open MeasureTheory

theorem QuantileMDP.theorem_3 {S A : Type*} [Fintype S] [Fintype A] (M : QuantileMDP.Model S A) (T : ℕ) :
    ∃ (act : ℕ → S → ℝ → A) (next : ℕ → S → ℝ → S → ℝ),
      (∀ t s τ, τ ∈ Set.Icc (0 : ℝ) 1 → act t s τ ∈ M.adm t s) ∧
      (∀ t < T, ∀ s τ, τ ∈ Set.Icc (0 : ℝ) 1 →
        let a := act t s τ
        let q := next t s τ
        let p := fun i => (M.P t s a i).toReal
        let g := fun i u => QuantileMDP.dpValue M T (t + 1) i u + (M.r t s a i : EReal)
        q ∈ QuantileMDP.Feasible p τ ∧
          (⨅ i, ⨅ (_ : q i ≠ 1), g i (q i)) = QuantileMDP.opt p g τ ∧
          QuantileMDP.opt p g τ = QuantileMDP.dpValue M T t s τ) ∧
      ∀ t s τ, τ ∈ Set.Icc (0 : ℝ) 1 →
        (M.shift t).Admissible (QuantileMDP.augmentedPolicy act next t τ) ∧
          QuantileMDP.quantile (QuantileMDP.rewardLaw (M.shift t) (T - t) (QuantileMDP.augmentedPolicy act next t τ) s) τ =
            QuantileMDP.dpValue M T t s τ := by sorry
