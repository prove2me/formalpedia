-- Prove2me | Theorems.Thm_SuttonBartoRL_AverageReward_differential_equations_shift_invariant
-- name    : SuttonBartoRL.AverageReward.differential_equations_shift_invariant
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T16:00:50.833135+00:00
-- url     : https://prove2.me/theorems/04dd7356-bd3e-4f2a-8062-7c6ce6688a84
-- title:
--   Differential Bellman equations and TD errors are unaffected by a common shift of the values
-- statement:
--   Let $\pi$ be a policy in a finite MDP, $\rho$ a real number (the average reward $r(\pi)$, or $\max_\pi r(\pi)$ in the optimality equations), and $c$ a real number. Then:
--   1. $v$ satisfies the differential Bellman equation for $v_\pi$, $v(s) = \sum_a\pi(a\mid s)\sum_{r,s'}p(s',r\mid s,a)[r-\rho+v(s')]$, if and only if $v + c$ does;
--   2. $q$ satisfies the differential Bellman equation for $q_\pi$ if and only if $q + c$ does;
--   3. $v$ satisfies the differential Bellman optimality equation for $v_*$ if and only if $v + c$ does;
--   4. $q$ satisfies the differential Bellman optimality equation for $q_*$ if and only if $q + c$ does;
--   5. the differential TD errors (10.10) and (10.11) are unchanged when $\hat v$ (resp. $\hat q$) is replaced by $\hat v + c$ (resp. $\hat q + c$):
--   $$
--   R - \bar R + (\hat v(s') + c) - (\hat v(s) + c) = R - \bar R + \hat v(s') - \hat v(s).
--   $$
--
--   This is why differential semi-gradient Sarsa converges only up to an arbitrary offset: the equations it solves determine differential values only up to a constant.
--
--   **Formalization Note** The action set is assumed nonempty so that the maxima in the optimality equations are defined.
-- source:
--   Sutton & Barto, Reinforcement Learning: An Introduction, 2nd ed., MIT Press (2018), ISBN 9780262039246, differential Bellman equations and Eqs. (10.10)–(10.11), p. 250

import Mathlib
import Definitions.Def_SuttonBartoRL_AverageReward_MDP
import Definitions.Def_SuttonBartoRL_AverageReward_AverageReward

namespace SuttonBartoRL.AverageReward

/-- Sutton & Barto (2018), p. 250: the differential Bellman equations for `v_π`, `q_π`, `v_*`, `q_*`
and the differential TD errors (10.10), (10.11) are unaffected if all the values are shifted by the
same amount `c`. The average-reward term `ρ` is arbitrary (the book's `r(π)` in the equations for
`v_π`, `q_π`, and `max_π r(π)` in those for `v_*`, `q_*`). -/
theorem differential_equations_shift_invariant {S A : Type} [Fintype S] [DecidableEq S]
    [Fintype A] [Nonempty A] (M : MDP S A) (π : SuttonBartoRL.FiniteMDP.Policy S A) (ρ c : ℝ) :
    (∀ v : S → ℝ, IsDiffBellmanV M π ρ v ↔ IsDiffBellmanV M π ρ (fun s => v s + c)) ∧
    (∀ q : S → A → ℝ, IsDiffBellmanQ M π ρ q ↔ IsDiffBellmanQ M π ρ (fun s a => q s a + c)) ∧
    (∀ v : S → ℝ, IsDiffBellmanOptV M ρ v ↔ IsDiffBellmanOptV M ρ (fun s => v s + c)) ∧
    (∀ q : S → A → ℝ, IsDiffBellmanOptQ M ρ q ↔ IsDiffBellmanOptQ M ρ (fun s a => q s a + c)) ∧
    (∀ (R Rbar : ℝ) (vhat : S → ℝ) (s s' : S),
      diffTDErrorV R Rbar (fun x => vhat x + c) s s' = diffTDErrorV R Rbar vhat s s') ∧
    (∀ (R Rbar : ℝ) (qhat : S → A → ℝ) (s : S) (a : A) (s' : S) (a' : A),
      diffTDErrorQ R Rbar (fun x b => qhat x b + c) s a s' a' = diffTDErrorQ R Rbar qhat s a s' a') := by sorry

end SuttonBartoRL.AverageReward
