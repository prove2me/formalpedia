-- Prove2me | Theorems.Thm_TiltingFTT_Optimal_welfare_improving_exists
-- name    : TiltingFTT.Optimal.welfare_improving_exists
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:26:05.474989+00:00
-- url     : https://prove2.me/theorems/6aee572b-4083-483f-b8a1-6b8056c94ab5
-- title:
--   Proof of Proposition 6, p. 48 — there exist admissible parameters with τ* < τ_0, so a welfare-improving FTT τ* exists
-- statement:
--   There exist parameters satisfying the standing assumptions, specification (23) with $v>0$, and the coexistence condition of Proposition 4 (ii) at $\tau=0$, such that
--   $$0<\tau^*<\tau_0\qquad\text{and}\qquad W_P<W_S(\tau^*).$$
--
--   In words: the hypotheses of the optimal-tax result can all be met at once, and then the tilting tax $\tau^*$ improves welfare relative to the Pareto-optimal pooling equilibrium.
--
--   **Formalization Note.** The paper derives this from the sufficient condition $v>\frac{V_H-V_L}{V_H+V_L}V_L$. That condition is not formalized because it is false as stated: the instance $V_H=5.6456$, $V_L=0.6891$, $v=0.6808$, $\beta=0.0198$, $\delta_I=1.6606$, $\delta_U=0.5910$ satisfies it together with all other assumptions but has $\tau^*\approx1.4597>\tau_0\approx1.4536$. Only the existence the paper concludes is stated.
-- source:
--   Dieler, Biswas, Calzolari & Castiglionesi, Asset Trade, Real Investment and a Tilting Financial Transaction Tax, accepted manuscript of January 24, 2022 (SSRN 2739357; Management Science 69(4), doi:10.1287/mnsc.2022.4417), proof of Proposition 6 (Appendix A), p. 48, "This shows that there exists indeed a welfare improving FTT τ*"

import Mathlib
import Definitions.Def_TiltingFTT_Optimal_Model

namespace TiltingFTT.Optimal

theorem welfare_improving_exists :
    ∃ (P : Firm) (VH VL v : ℝ), Standing P ∧ Spec23 P VH VL v ∧ 0 < v ∧ Coexist P 0 ∧
      tauStar P < tau0 P v ∧ 0 < tauStar P ∧ poolWelfare P 0 1 < WS P (tauStar P) := by sorry

end TiltingFTT.Optimal
