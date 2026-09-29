-- Prove2me | Theorems.Thm_RobustLP_Counterpart_star_iff_exists_irc
-- name    : RobustLP.Counterpart.star_iff_exists_irc
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T19:28:25.293976+00:00
-- url     : https://prove2.me/theorems/dc2e12d7-fdb9-4b77-9c3c-5a3fce245c94
-- title:
--   (∗) is equivalent to the LP (IRC[$\epsilon,\delta$])
-- statement:
--   Let an uncertain linear program with uncertain-entry sets $J_i$ be given, and let $\epsilon>0$, $\delta>0$. A vector $x$ is feasible for problem (∗),
--   $$
--   Ex=e,\quad Ax\le b,\quad \sum_j a_{ij}x_j+\epsilon\sum_{j\in J_i}|a_{ij}||x_j|\le b_i+\delta\max[1,|b_i|]\ \forall i,\quad \ell\le x\le u,
--   $$
--   if and only if there is $y\in\mathbb{R}^n$ such that $(x,y)$ is feasible for the interval robust counterpart
--   $$
--   Ex=e,\quad Ax\le b,\quad \sum_j a_{ij}x_j+\epsilon\sum_{j\in J_i}|a_{ij}|\,y_j\le b_i+\delta\max[1,|b_i|]\ \forall i,\quad -y_j\le x_j\le y_j\ \forall j,\quad \ell\le x\le u. \tag{IRC[$\epsilon,\delta$]}
--   $$
--   Since both problems minimize $c^Tx$, they are equivalent optimization problems.
--
--   Together with the characterization of reliable solutions by (∗), this shows that a robust optimal solution can be computed by solving a single linear program (Soyster's scheme).
--
--   **Formalization Note** "Equivalent" is formalized as equality of the projections of the feasible sets onto $x$. The misprint $a_{ij}x_i$ of the printed (IRC) is corrected to $a_{ij}x_j$.
-- source:
--   Ben-Tal and Nemirovski, Robust solutions of Linear Programming problems contaminated with uncertain data, Math. Program. Ser. A 88 (2000) 411–424, pp. 417–418, §3.1, 'It is easily seen that (∗) is equivalent to the Linear Programming program … (IRC[ϵ, δ])'

import Mathlib
import Definitions.Def_RobustLP_Counterpart_UncertainLP
import Definitions.Def_RobustLP_Counterpart_RobustCounterparts

namespace RobustLP.Counterpart

/-- **(∗) is equivalent to (IRC[ε, δ])** (Ben-Tal–Nemirovski 2000, §3.1, pp. 417–418). For `ε > 0`
and `δ > 0`, `x` is feasible for (∗) if and only if there is `y` with `(x, y)` feasible for the
interval robust counterpart (IRC[ε, δ]). (Both problems minimize the same objective `cᵀx`.) -/
theorem star_iff_exists_irc {n p m : ℕ} (L : UncertainLP n p m)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (x : Fin n → ℝ) :
    L.StarFeasible ε δ x ↔ ∃ y : Fin n → ℝ, L.IRCFeasible ε δ x y := by sorry

end RobustLP.Counterpart
