-- Prove2me | Theorems.Thm_PerimeterPatrol_Visible_theorem_2
-- name    : PerimeterPatrol.Visible.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:42.120981+00:00
-- url     : https://prove2.me/theorems/4e12e00d-7c10-4748-8807-aab3cbe59e3f
-- title:
--   Theorem 2, pp. 6–7 — the blue–red schedule is optimal in Γ(λ, t, p) against an observing attacker, the value is (2), and it increases in λ, t, p
-- statement:
--   **Theorem 2.** Let $\lambda > 0$, $t > 0$ and $p \in (0, 1]$, and consider the Stackelberg patrol game $\Gamma(\lambda, t, p)$: the defender commits to a feasible mixed strategy (dispatch rate $\lambda$, condition (1)); the attacker watches the patrollers go by and starts an attack of duration $t$ inside an operating window $[y, z]$, $0 < y$; each passing patroller detects independently with probability $p$. Let $\mu^*$ be the schedule with blue patrollers at $jt + k\Delta$ ($\Delta = t/\lceil \lambda t \rceil$, $j \ge 0$, $1 \le k \le \lfloor \lambda t \rfloor$) and a red patroller at each $jt$ independently with probability $\lambda t - \lfloor \lambda t \rfloor$ (fixed intervals $1/\lambda$ when $\lambda t$ is an integer). Then:
--
--   1. $\mu^*$ is a feasible mixed strategy;
--   2. against $\mu^*$, every attack $\tau$ is detected with probability at least
--   $$V(\lambda, t, p) = 1 - (\lambda t - \lfloor \lambda t \rfloor)(1 - p)^{\lceil \lambda t \rceil} - (1 - \lambda t + \lfloor \lambda t \rfloor)(1 - p)^{\lfloor \lambda t \rfloor};$$
--   3. against every feasible mixed strategy $\mu$ and every $\varepsilon > 0$ there is an attack detected with probability less than $V(\lambda, t, p) + \varepsilon$;
--   4. $V$ is nondecreasing in $\lambda$, in $t$ and in $p$.
--
--   Items 2 and 3 together say that the Stackelberg value $\sup_\mu \inf_\tau P_{\mathrm{det}}(\mu, \tau)$ equals $V(\lambda, t, p)$ and that $\mu^*$ attains the supremum, i.e. $\mu^*$ is the defender's optimal strategy and (2) is the value of the game.
--
--   The point of the theorem is that an attacker who can see the patrollers gains nothing: a suitably randomised schedule makes every attack meet the least-variance number of patrollers of Lemma 1, whatever the attacker has observed.
--
--   **Formalization Note.** Attacks occupy $(\tau, \tau + t]$ and may use all arrivals in $[0, \tau]$ (observation from time $0$ instead of $y$ enlarges the attacker class, so item 2 is at least as strong as the page). The value is not defined through real suprema and infima; items 2 and 3 state it directly. "Increases" is weak monotonicity, since $V \equiv 1$ at $p = 1$, $\lambda t \ge 1$.
-- source:
--   Lin, Optimal Patrol of a Perimeter, arXiv:1905.03600v3, pp. 6–7, Theorem 2 (proof pp. 7–8)

import Mathlib
import Definitions.Def_PerimeterPatrol_Visible_Model
import Definitions.Def_PerimeterPatrol_Visible_OptimalPatrol

open MeasureTheory

namespace PerimeterPatrol.Visible
theorem theorem_2 (lam t p : ℝ) (hlam : 0 < lam) (ht : 0 < t) (hp0 : 0 < p) (hp1 : p ≤ 1) : IsMixedStrategy lam (optimalPatrol lam t) ∧ (∀ τ : (ℕ → ℝ) → ℝ, IsAttack t τ → patrolValue lam t p ≤ detectionProb p t (optimalPatrol lam t) τ) ∧ (∀ μ : Measure (ℕ → ℝ), IsMixedStrategy lam μ → ∀ ε : ℝ, 0 < ε → ∃ τ : (ℕ → ℝ) → ℝ, IsAttack t τ ∧ detectionProb p t μ τ < patrolValue lam t p + ε) ∧ (MonotoneOn (fun l : ℝ => patrolValue l t p) (Set.Ioi 0) ∧ MonotoneOn (fun u : ℝ => patrolValue lam u p) (Set.Ioi 0) ∧ MonotoneOn (fun q : ℝ => patrolValue lam t q) (Set.Ioc 0 1)) := by sorry
end PerimeterPatrol.Visible
