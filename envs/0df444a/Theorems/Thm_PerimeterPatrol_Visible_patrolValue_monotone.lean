-- Prove2me | Theorems.Thm_PerimeterPatrol_Visible_patrolValue_monotone
-- name    : PerimeterPatrol.Visible.patrolValue_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:24:12.786979+00:00
-- url     : https://prove2.me/theorems/4b0cc85a-40cc-4826-8bdc-dc262b7633bb
-- title:
--   Theorem 2, proof, p. 8 — V(λ, t, p) increases in each of λ, t and p
-- statement:
--   Let $\lambda > 0$, $t > 0$, $p \in (0, 1]$, and let
--
--   $$V(\lambda, t, p) = 1 - (\lambda t - \lfloor \lambda t \rfloor)(1 - p)^{\lceil \lambda t \rceil} - (1 - \lambda t + \lfloor \lambda t \rfloor)(1 - p)^{\lfloor \lambda t \rfloor}$$
--
--   be the value (2). Then
--
--   1. $\lambda' \mapsto V(\lambda', t, p)$ is nondecreasing on $(0, \infty)$;
--   2. $t' \mapsto V(\lambda, t', p)$ is nondecreasing on $(0, \infty)$;
--   3. $p' \mapsto V(\lambda, t, p')$ is nondecreasing on $(0, 1]$.
--
--   More patrol effort, longer attacks and more reliable patrollers never lower the defender's value.
--
--   **Formalization Note.** "Increases" is read as nondecreasing: at $p = 1$ and $\lambda t \ge 1$ the value is identically $1$, so strict monotonicity is false.
-- source:
--   Lin, Optimal Patrol of a Perimeter, arXiv:1905.03600v3, pp. 7–8, Theorem 2 ('which increases in λ, t, and p') and its proof, last sentence

import Mathlib
import Definitions.Def_PerimeterPatrol_Visible_Model

namespace PerimeterPatrol.Visible
theorem patrolValue_monotone (lam t p : ℝ) (hlam : 0 < lam) (ht : 0 < t) (hp0 : 0 < p) (hp1 : p ≤ 1) : MonotoneOn (fun l : ℝ => patrolValue l t p) (Set.Ioi 0) ∧ MonotoneOn (fun u : ℝ => patrolValue lam u p) (Set.Ioi 0) ∧ MonotoneOn (fun q : ℝ => patrolValue lam t q) (Set.Ioc 0 1) := by sorry
end PerimeterPatrol.Visible
