-- Prove2me | Theorems.Thm_PerimeterPatrol_Visible_blue_red_count
-- name    : PerimeterPatrol.Visible.blue_red_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:01.20002+00:00
-- url     : https://prove2.me/theorems/a101ce8d-f732-4d18-b9ce-1b740da07ee5
-- title:
--   Theorem 2, proof, p. 7 — every attack window of length t holds exactly ⌊λt⌋ blue time points and exactly one red slot
-- statement:
--   Let $\lambda > 0$, $t > 0$, $\Delta = t / \lceil \lambda t \rceil$, and let $a \ge 0$. Consider the blue time points $jt + k\Delta$ ($j = 0, 1, 2, \dots$, $k = 1, \dots, \lfloor \lambda t \rfloor$) and the red slots $jt$ ($j = 0, 1, 2, \dots$) of Theorem 2. Then the window $(a, a + t]$ contains
--
--   1. exactly $\lfloor \lambda t \rfloor$ blue time points (counted by index $(j, k)$), and
--   2. exactly one red slot $jt$.
--
--   $$\#\{(j,k) : 1 \le k \le \lfloor \lambda t \rfloor,\ a < jt + k\Delta \le a + t\} = \lfloor \lambda t \rfloor, \qquad \#\{j : a < jt \le a + t\} = 1 .$$
--
--   This is the deterministic part of the claim that "regardless of when the attack begins, any attack period will encounter exactly $\lfloor \lambda t \rfloor$ blue patrollers, and 1 red patroller with probability $\lambda t - \lfloor \lambda t \rfloor$": the count of blue patrollers does not depend on where the attack starts, and the only randomness an attack meets is a single red slot.
--
--   **Formalization Note.** The page states this when $\lambda t$ is not an integer; the statement here has no such hypothesis, and in the integer case it says that every window of length $t$ holds exactly $\lambda t$ of the points $m/\lambda$, $m \ge 1$. The window is half-open, $(a, a + t]$, the attack-window convention of the mission; $a \ge 0$ because attacks start after time $0$.
-- source:
--   Lin, Optimal Patrol of a Perimeter, arXiv:1905.03600v3, p. 7, Theorem 2, proof, 'Regardless of when the attack begins, any attack period will encounter exactly ⌊λt⌋ blue patrollers …'

import Mathlib
import Definitions.Def_PerimeterPatrol_Visible_Model
import Definitions.Def_PerimeterPatrol_Visible_OptimalPatrol

namespace PerimeterPatrol.Visible
theorem blue_red_count (lam t a : ℝ) (hlam : 0 < lam) (ht : 0 < t) (ha : 0 ≤ a) : Nat.card {jk : ℕ × ℕ | IsBlue lam t jk ∧ a < bluePoint lam t jk ∧ bluePoint lam t jk ≤ a + t} = ⌊lam * t⌋₊ ∧ Nat.card {j : ℕ | a < (j : ℝ) * t ∧ (j : ℝ) * t ≤ a + t} = 1 := by sorry
end PerimeterPatrol.Visible
