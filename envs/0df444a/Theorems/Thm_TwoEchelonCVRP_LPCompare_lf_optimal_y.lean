-- Prove2me | Theorems.Thm_TwoEchelonCVRP_LPCompare_lf_optimal_y
-- name    : TwoEchelonCVRP.LPCompare.lf_optimal_y
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:08:46.213859+00:00
-- url     : https://prove2.me/theorems/21e784fa-fcfa-4a06-b125-f9e306dd672f
-- title:
--   §3, remark on LF — in an optimal LF solution, $y_r = (\sum_{k\in R_r} q_{kr})/Q_1$ (when every $g_r > 0$)
-- statement:
--   Consider a 2E-CVRP instance with first-level routes $\mathcal M$ and second-level routes $\mathcal R$, and suppose every first-level route has positive cost, $g_r > 0$ for all $r \in \mathcal M$. Then every optimal solution $(x, y, q)$ of the LP relaxation $LF$ satisfies
--   $$y_r = \frac{\sum_{k \in R_r} q_{kr}}{Q_1} \qquad \text{for every } r \in \mathcal M.$$
--
--   In words, the LP relaxation charges each first-level route only the fraction of its cost proportional to the load it carries. This is why $z(LF)$ deteriorates as the first-level routing cost grows, which motivates the stronger relaxation $RF$.
--
--   **Formalization Note.** The paper states the identity for "any optimal $LF$ solution" without a hypothesis on $g_r$. If some $g_r = 0$, the value of $y_r$ can be raised at no cost and the identity fails for some optimal solutions, so the hypothesis $g_r > 0$ for all $r$ is added. It holds whenever the travel costs or the first-level fixed cost $U_1$ are positive.
-- source:
--   Baldacci, Mingozzi, Roberti & Wolfler Calvo, An Exact Algorithm for the Two-Echelon Capacitated Vehicle Routing Problem, Oper. Res. 61(2) (2013), p. 301, §3, the remark on LF

import Mathlib
import Definitions.Def_TwoEchelonCVRP_LPCompare_Relaxations

namespace TwoEchelonCVRP.LPCompare

open Finset

/-- **§3, the remark on `LF` (Baldacci et al. 2013, p. 301).** If every first-level route has
positive cost `g_r > 0`, then in every optimal solution of the LP relaxation `LF`,
`y_r = (∑_{k ∈ R_r} q_{kr}) / Q₁` for every first-level route `r`. The hypothesis `g_r > 0` is
added: with `g_r = 0` the value of `y_r` can be raised at no cost. -/
theorem lf_optimal_y {I : Instance} (RS : RouteSystem I) (hg : ∀ r, 0 < RS.g r)
    (p : LFPoint RS) (hp : IsOptimalLF p) :
    ∀ r, p.y r = (∑ k ∈ RS.R1 r, p.qd r k) / (I.Q1 : ℝ) := by sorry

end TwoEchelonCVRP.LPCompare
