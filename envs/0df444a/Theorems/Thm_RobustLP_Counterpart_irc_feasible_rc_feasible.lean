-- Prove2me | Theorems.Thm_RobustLP_Counterpart_irc_feasible_rc_feasible
-- name    : RobustLP.Counterpart.irc_feasible_rc_feasible
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:29:02.530725+00:00
-- url     : https://prove2.me/theorems/34cf4f86-0610-46d0-87e4-b4e2acd9703f
-- title:
--   (RC[$\epsilon,\delta,\Omega$]) is less conservative than (IRC[$\epsilon,\delta$])
-- statement:
--   Let an uncertain linear program with uncertain-entry sets $J_i$ be given, and let $\epsilon>0$, $\delta>0$, $\Omega>0$. If $(x,y)$ is feasible for the interval robust counterpart (IRC[ε, δ]), then $(x, y', z')$ with
--   $$
--   y'_{ij} = y_j,\qquad z'_{ij} = 0\qquad\text{for all } i, j
--   $$
--   is feasible for the robust counterpart (RC[ε, δ, Ω]).
--
--   Every $x$ admissible for the linear counterpart is therefore admissible for the conic one, so the optimal value of (RC) is at most that of (IRC).
--
--   **Formalization Note** The page does not state the sign of $\Omega$; the hypothesis $\Omega>0$ is carried for uniformity with Proposition 1, where (RC) is introduced with a positive parameter.
-- source:
--   Ben-Tal and Nemirovski, Robust solutions of Linear Programming problems contaminated with uncertain data, Math. Program. Ser. A 88 (2000) 411–424, p. 420, §3.1, 'Note that (RC[ϵ, δ, Ω]) is "less conservative" that (IRC[ϵ, δ])'

import Mathlib
import Definitions.Def_RobustLP_Counterpart_UncertainLP
import Definitions.Def_RobustLP_Counterpart_RobustCounterparts

namespace RobustLP.Counterpart

/-- **(RC) is less conservative than (IRC)** (Ben-Tal–Nemirovski 2000, §3.1, p. 420). For
`ε > 0`, `δ > 0`, `Ω > 0`: if `(x, y)` is feasible for (IRC[ε, δ]), then `(x, y', z')` with
`y'_{ij} = y_j` and `z'_{ij} = 0` is feasible for (RC[ε, δ, Ω]). -/
theorem irc_feasible_rc_feasible {n p m : ℕ} (L : UncertainLP n p m)
    (ε δ Ω : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hΩ : 0 < Ω) (x y : Fin n → ℝ)
    (hIRC : L.IRCFeasible ε δ x y) :
    L.RCFeasible ε δ Ω x (fun _ j => y j) (fun _ _ => 0) := by sorry

end RobustLP.Counterpart
