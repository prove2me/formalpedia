-- Prove2me | Theorems.Thm_TiltingFTT_Optimal_tauStar_step
-- name    : TiltingFTT.Optimal.tauStar_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:56.865502+00:00
-- url     : https://prove2.me/theorems/b9cf1da7-c0c9-40ea-a727-76d5d9de5fc7
-- title:
--   Proof of Proposition 6, p. 48 — from pooling at τ = 0, τ* > 0 and pooling exists exactly for τ ≤ τ*
-- statement:
--   Assume the standing assumptions and that at $\tau=0$ the economy lies in the coexistence region of Proposition 4 (ii): $$\frac{\bar F}{\bar F_L}<\frac{\delta_I}{\delta_U}\le\min\Big\{\frac{F_H-\bar F}{F_H-\bar F_H},\frac{F_H-F_L}{F_H-F^L_H}\Big\}.$$ Then
--
--   1. $\tau^*=\frac{\delta_I}{\delta_U}\frac{\bar F_L}{\bar F}-1>0$;
--   2. for every $\tau\ge0$, a pooling equilibrium (with any trade level $T_P$) exists if and only if $\tau\le\tau^*$;
--   3. $\tau^*<\tau_{FB}=\delta_I/\delta_U-1$.
--
--   So $\tau^*$ is the threshold tax beyond which the pooling equilibrium ceases to exist, whatever its level of trade.
--
--   **Formalization Note.** The proof writes $\delta_I/\delta_U\ge\bar F/\bar F_L$ and concludes that $\tau^*$ is "positive"; strict positivity requires the strict inequality, taken from Proposition 4 (ii) at $\tau=0$. Because (22) is closed, the pooling equilibrium still exists at $\tau=\tau^*$ itself.
-- source:
--   Dieler, Biswas, Calzolari & Castiglionesi, Asset Trade, Real Investment and a Tilting Financial Transaction Tax, accepted manuscript of January 24, 2022 (SSRN 2739357; Management Science 69(4), doi:10.1287/mnsc.2022.4417), proof of Proposition 6 (Appendix A), p. 48, "This implies that the smallest FTT which makes the pooling equilibrium cease to exist, i.e. τ* = (δI/δU)(F̄L/F̄) − 1 is positive"

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model

namespace TiltingFTT.Optimal

theorem tauStar_step (P : Firm) (hS : Standing P) (h0 : Coexist P 0) :
    0 < tauStar P ∧
    (∀ τ, 0 ≤ τ → ((∃ TP, IsPoolingEq P τ TP) ↔ τ ≤ tauStar P)) ∧
    tauStar P < tauFB P := by sorry

end TiltingFTT.Optimal
