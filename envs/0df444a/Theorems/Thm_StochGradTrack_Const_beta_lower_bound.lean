-- Prove2me | Theorems.Thm_StochGradTrack_Const_beta_lower_bound
-- name    : StochGradTrack.Const.beta_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T12:44:50.687701+00:00
-- url     : https://prove2.me/theorems/5f642793-2c86-4e5d-9dec-6102dab8c1c0
-- title:
--   (27), p. 422 — if α ≤ (1 − ρ_w²)/(12ρ_wL) then β ≥ (1 − ρ_w²)/(8ρ_w²) > 0
-- statement:
--   Let $0<\rho<1$, $L>0$ and $0<\alpha\le\frac{1-\rho^2}{12\rho L}$, and let $\beta=\frac{1-\rho^2}{2\rho^2}-4\alpha L-2\alpha^2L^2$. Then
--   $$\beta\ge\frac{1-\rho^2}{2\rho^2}-\frac{1-\rho^2}{3\rho}-\frac{(1-\rho^2)^2}{72\rho^2}\ge\frac{11(1-\rho^2)}{72\rho^2}\ge\frac{1-\rho^2}{8\rho^2}>0 .$$
--
--   The first term of (7) makes Theorem 1's $\beta$ positive and bounded below, so the matrix of Theorem 1 is the matrix of (21) for an admissible $\beta$.
--
--   **Formalization Note.** All four inequalities of the chain are stated (the last two combined as $\frac{1-\rho^2}{8\rho^2}\le\beta$ and $0<\beta$).
-- source:
--   Pu & Nedić, Math. Program. 187 (2021), §3.1, (27), p. 422

import Mathlib
import Definitions.Def_StochGradTrack_Const_Matrix

namespace StochGradTrack.Const

open MeasureTheory ProbabilityTheory Matrix

theorem beta_lower_bound (α L ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hL : 0 < L) (hα : 0 < α)
    (h7a : α ≤ (1 - ρ ^ 2) / (12 * ρ * L)) :
    (1 - ρ ^ 2) / (2 * ρ ^ 2) - (1 - ρ ^ 2) / (3 * ρ) - (1 - ρ ^ 2) ^ 2 / (72 * ρ ^ 2)
        ≤ betaT α L ρ ∧
      11 * (1 - ρ ^ 2) / (72 * ρ ^ 2) ≤
        (1 - ρ ^ 2) / (2 * ρ ^ 2) - (1 - ρ ^ 2) / (3 * ρ) - (1 - ρ ^ 2) ^ 2 / (72 * ρ ^ 2) ∧
      (1 - ρ ^ 2) / (8 * ρ ^ 2) ≤ betaT α L ρ ∧ 0 < betaT α L ρ := by sorry

end StochGradTrack.Const
