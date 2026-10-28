-- Prove2me | Theorems.Thm_TiltingFTT_Optimal_welfare_24_25
-- name    : TiltingFTT.Optimal.welfare_24_25
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:50.62898+00:00
-- url     : https://prove2.me/theorems/34ce2f2e-60dd-4669-a030-23b178a940c8
-- title:
--   (8), (24), (25), pp. 13, 24–25 — first-best, separating and pooling welfare
-- statement:
--   For any parameters, any tax $\tau$ and any $T_L$, evaluating the welfare bracket of (8) gives:
--
--   1. at full trade with full information (prices $\delta_UF_\omega$, trades $1$, values $F_\omega$): $W^*=\delta_I(\beta F_H+(1-\beta)F_L)$;
--   2. in a separating profile with $T_H=1$: $$W_S=W^*-(1-\beta)(\delta_I-\delta_U)(1-T_L)F_L;\qquad (24)$$
--   3. in the pooling profile with $T_P=1$: $$W_P=W^*-\delta_I\big(\beta(F_H-\bar F_H)+(1-\beta)(F_L-\bar F_L)\big);\qquad (25)$$
--   4. under specification (23), $W_P=W^*-\delta_Iv$.
--
--   The tax and the price payments are transfers and cancel in welfare, so neither $W_S$ nor $W_P$ depends on $\tau$ directly; $W_S$ depends on $\tau$ only through the equilibrium trade $T_L$.
-- source:
--   Dieler, Biswas, Calzolari & Castiglionesi, Asset Trade, Real Investment and a Tilting Financial Transaction Tax, accepted manuscript of January 24, 2022 (SSRN 2739357; Management Science 69(4), doi:10.1287/mnsc.2022.4417), (8), p. 14; (24), p. 24; (25), p. 25

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model

namespace TiltingFTT.Optimal

theorem welfare_24_25 (P : Firm) (τ TL VH VL v : ℝ) :
    welfare P τ (P.δU * P.FH) (P.δU * P.FL) 1 1 P.FH P.FL = Wstar P ∧
    sepWelfare P τ 1 TL = Wstar P - (1 - P.β) * (P.δI - P.δU) * (1 - TL) * P.FL ∧
    poolWelfare P τ 1 =
      Wstar P - P.δI * (P.β * (P.FH - P.FbH) + (1 - P.β) * (P.FL - P.FbL)) ∧
    (Spec23 P VH VL v → poolWelfare P τ 1 = Wstar P - P.δI * v) := by sorry

end TiltingFTT.Optimal
