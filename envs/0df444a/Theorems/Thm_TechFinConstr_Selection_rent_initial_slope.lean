-- Prove2me | Theorems.Thm_TechFinConstr_Selection_rent_initial_slope
-- name    : TechFinConstr.Selection.rent_initial_slope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:39.364426+00:00
-- url     : https://prove2.me/theorems/9ac0e94f-c2a2-49d7-b261-67371b2d3414
-- title:
--   Proof of Proposition 6, p. 47 — the agency rent equals c/Φ*(p) on an initial interval (0, c₁]
-- statement:
--   In Starmans' model, let $p\in\mathscr P$. There is a $c_1$ with $0<c_1\le\pi$ such that for every $c\in(0,c_1]$, problem (1) has an optimal contract and every optimal contract $s$ has agency rent
--   $$\mathbb E_q[s]=\frac{c}{\Phi^*(p)} .$$
--
--   That is, the agency rent function starts linearly with slope $1/\Phi^*(p)$, the reciprocal of the maximum cumulative likelihood ratio (one can take $c_1=\bar c_1$ of Proposition 1). Comparing these initial slopes decides which entrepreneur is cheaper for small disutility of effort in Proposition 6.
-- source:
--   Starmans, Technological Determinants of Financial Constraints, manuscript (February 4, 2022), p. 47, Appendix A.14 (proof of Proposition 6): "The initial slope of the agency rent function for p″ is given by 1/Φ*(p″)."

import Mathlib
import Definitions.Def_TechFinConstr_Selection_Model

namespace TechFinConstr.Selection

theorem rent_initial_slope {n : ℕ} (E : Economy n) (hE : E.Standing)
    (p : Fin (n + 1) → ℝ) (hp : InP E p) :
    ∃ c₁, 0 < c₁ ∧ c₁ ≤ E.piE ∧
      ∀ c, 0 < c → c ≤ c₁ →
        (∃ s, IsOptimalContract E p c s) ∧
        ∀ s, IsOptimalContract E p c s → expect E.q s = c / PhiStar E p := by sorry

end TechFinConstr.Selection
