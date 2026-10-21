-- Prove2me | Theorems.Thm_PerimeterPatrol_Visible_optimalPatrol_detection_eq
-- name    : PerimeterPatrol.Visible.optimalPatrol_detection_eq
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:11.555973+00:00
-- url     : https://prove2.me/theorems/7d32a8fd-a116-46d2-a955-846f91ac9ec1
-- title:
--   Theorem 2, proof, p. 7 — the blue–red schedule detects every adaptive attack with probability exactly V(λ, t, p)
-- statement:
--   Let $\lambda > 0$, $t > 0$, $p \in (0, 1]$, and let $\mu^*$ be the blue–red schedule of Theorem 2. For every attack $\tau$ — a start-time rule inside a fixed operating window $[y, z]$, $0 < y$, that may depend on all patrollers seen up to the moment it starts — the detection probability is exactly the value (2):
--
--   $$P_{\mathrm{det}}(\mu^*, \tau) = 1 - (\lambda t - \lfloor \lambda t \rfloor)(1 - p)^{\lceil \lambda t \rceil} - (1 - \lambda t + \lfloor \lambda t \rfloor)(1 - p)^{\lfloor \lambda t \rfloor} = V(\lambda, t, p).$$
--
--   In the paper's words (p. 7), each attack meets $\lceil \lambda t \rceil$ patrollers with probability $\lambda t - \lfloor \lambda t \rfloor$ and $\lfloor \lambda t \rfloor$ patrollers otherwise, however it uses what it has observed; so the defender guarantees (2). When $\lambda t$ is an integer, every attack meets exactly $\lambda t$ patrollers and the detection probability is $1 - (1 - p)^{\lambda t}$, which is (2).
--
--   **Formalization Note.** The attack window is $(\tau, \tau + t]$ and the attacker may use the arrivals in $[0, \tau]$, including a patroller passing exactly at $\tau$; observing from time $0$ rather than from $y$ only enlarges the attacker's options, so this statement is at least as strong as the page's. The page states the guarantee ("guarantees the detection probability in (2)"); the equality stated here is what its argument establishes.
-- source:
--   Lin, Optimal Patrol of a Perimeter, arXiv:1905.03600v3, p. 7, Theorem 2, proof, first paragraph

import Mathlib
import Definitions.Def_PerimeterPatrol_Visible_Model
import Definitions.Def_PerimeterPatrol_Visible_OptimalPatrol

namespace PerimeterPatrol.Visible
theorem optimalPatrol_detection_eq (lam t p : ℝ) (hlam : 0 < lam) (ht : 0 < t) (hp0 : 0 < p) (hp1 : p ≤ 1) (τ : (ℕ → ℝ) → ℝ) (hτ : IsAttack t τ) : detectionProb p t (optimalPatrol lam t) τ = patrolValue lam t p := by sorry
end PerimeterPatrol.Visible
