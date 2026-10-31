-- Prove2me | Theorems.Thm_SwitchCostGames_Stationary_value_le_pure_minimax
-- name    : SwitchCostGames.Stationary.value_le_pure_minimax
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:13.811778+00:00
-- url     : https://prove2.me/theorems/013fa716-d856-44e3-b86f-5bd98ad8a6af
-- title:
--   Proof of Theorem 1 — $v(c)$ is bounded by the pure minimax $\min_j \max_i a_{ij}$ of $A$
-- statement:
--   Let $\Gamma = (A,S,c)$ be a zero-sum game with switching costs with $m,n\ge1$ and $c\ge0$. If $v$ is the value of the repeated game in stationary strategies, then $v$ is at most the pure minimax of $A$:
--   $$
--   v \ \le\ \min_{j\in[n]} \max_{i\in[m]} a_{ij}.
--   $$
--
--   The bound does not depend on $c$. Together with monotonicity and concavity of $c\mapsto v(c)$ it forces $v$ to be eventually constant, which is part of Theorem 1.
-- source:
--   Tsodikovich, Venel & Zseleva, The Regularity of the Value Function of Repeated Games with Switching Costs, Math. Oper. Res., Articles in Advance (2 Nov 2022), doi:10.1287/moor.2022.1325, p. 3 (PDF 5), proof of Theorem 1, second paragraph

import Mathlib
import Definitions.Def_SwitchCostGames_Stationary_Model

namespace SwitchCostGames.Stationary

theorem value_le_pure_minimax {m n : ℕ} [NeZero m] [NeZero n] (G : Game m n) (c v : ℝ)
    (hc : 0 ≤ c) (hv : IsValue G c v) :
    v ≤ Finset.univ.inf' Finset.univ_nonempty
      (fun j : Fin n => Finset.univ.sup' Finset.univ_nonempty (fun i : Fin m => G.A i j)) := by sorry

end SwitchCostGames.Stationary
