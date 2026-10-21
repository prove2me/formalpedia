-- Prove2me | Theorems.Thm_TiltingFTT_Optimal_proposition_4
-- name    : TiltingFTT.Optimal.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:54.181433+00:00
-- url     : https://prove2.me/theorems/2d33f940-9292-456f-8fb5-fd3da30d1495
-- title:
--   Proposition 4, p. 22 — only separating equilibria when 1 ≤ δ_I/(δ_U(1+τ)) < F̄/F̄_L; both types in the coexistence region
-- statement:
--   Assume the standing assumptions and fix $\tau\ge0$.
--
--   1. If $1\le\frac{\delta_I}{\delta_U(1+\tau)}<\frac{\bar F}{\bar F_L}$, a separating equilibrium exists and no pooling equilibrium exists.
--   2. If $$\frac{\bar F}{\bar F_L}<\frac{\delta_I}{\delta_U(1+\tau)}\le\min\Big\{\frac{F_H-\bar F}{F_H-\bar F_H},\ \frac{F_H-F_L}{F_H-F^L_H}\Big\},$$ both a separating and a pooling equilibrium exist.
--
--   The proposition maps the adjusted liquidity ratio to the types of equilibrium that can arise; the coexistence region in (ii) is the starting point of the optimal-tax analysis.
--
--   **Formalization Note.** The paper prints item (i) with "$\le\bar F/\bar F_L$". At equality condition (22) can hold and a pooling equilibrium then exists by Proposition 3, so the printed (i) is false there; it is stated with the strict inequality. All ratio conditions are cross-multiplied.
-- source:
--   Dieler, Biswas, Calzolari & Castiglionesi, Asset Trade, Real Investment and a Tilting Financial Transaction Tax, accepted manuscript of January 24, 2022 (SSRN 2739357; Management Science 69(4), doi:10.1287/mnsc.2022.4417), Proposition 4, p. 22

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model

namespace TiltingFTT.Optimal

theorem proposition_4 (P : Firm) (τ : ℝ) (hS : Standing P) (hτ : 0 ≤ τ) :
    (Cond15 P τ → P.δI * P.FbL < (1 + τ) * P.δU * Fbar P →
      (∃ TH TL, IsSeparatingEq P τ TH TL) ∧ ¬ ∃ TP, IsPoolingEq P τ TP) ∧
    (Coexist P τ →
      (∃ TH TL, IsSeparatingEq P τ TH TL) ∧ ∃ TP, IsPoolingEq P τ TP) := by sorry

end TiltingFTT.Optimal
