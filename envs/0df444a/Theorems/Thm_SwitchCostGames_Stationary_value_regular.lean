-- Prove2me | Theorems.Thm_SwitchCostGames_Stationary_value_regular
-- name    : SwitchCostGames.Stationary.value_regular
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:18.209847+00:00
-- url     : https://prove2.me/theorems/b1918abf-9453-41bc-8793-8134a45ecc0b
-- title:
--   Proof of Theorem 1 — $v(c)$ is continuous, increasing, concave and piecewise linear on $[0,\infty)$
-- statement:
--   Let $\Gamma = (A,S,\cdot)$ be a game with switching costs with $m,n\ge1$, and let $v(c)$ be the value of the repeated game in stationary strategies for every switching-cost weight $c \ge 0$. Then on $[0,\infty)$ the function
--   $$
--   c \longmapsto v(c)
--   $$
--   is continuous, increasing (nondecreasing), concave, and piecewise linear with finitely many pieces.
--
--   In the paper this is obtained by applying Lemma 1 to the one-shot game of the Filar–Raghavan reduction along the diagonal $x = (c,\dots,c)$. It is the regularity part of Theorem 1.
--
--   **Formalization Note** "Increasing" is `MonotoneOn` (nondecreasing): $v$ is eventually constant, so it is not strictly increasing in general. Piecewise linearity is the finite-breakpoint predicate of the model file on $[0,\infty)$.
-- source:
--   Tsodikovich, Venel & Zseleva, The Regularity of the Value Function of Repeated Games with Switching Costs, Math. Oper. Res., Articles in Advance (2 Nov 2022), doi:10.1287/moor.2022.1325, p. 3 (PDF 5), proof of Theorem 1, second paragraph

import Mathlib
import Definitions.Def_SwitchCostGames_Stationary_Model

namespace SwitchCostGames.Stationary

theorem value_regular {m n : ℕ} [NeZero m] [NeZero n] (G : Game m n) (v : ℝ → ℝ)
    (hv : ∀ c : ℝ, 0 ≤ c → IsValue G c (v c)) :
    ContinuousOn v (Set.Ici 0) ∧ MonotoneOn v (Set.Ici 0) ∧ ConcaveOn ℝ (Set.Ici 0) v ∧
      IsPiecewiseAffineOn v (Set.Ici 0) := by sorry

end SwitchCostGames.Stationary
