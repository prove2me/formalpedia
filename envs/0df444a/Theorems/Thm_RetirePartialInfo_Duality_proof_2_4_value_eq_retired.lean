-- Prove2me | Theorems.Thm_RetirePartialInfo_Duality_proof_2_4_value_eq_retired
-- name    : RetirePartialInfo.Duality.proof_2_4_value_eq_retired
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T05:40:45.762998+00:00
-- url     : https://prove2.me/theorems/fda75039-dd44-4e61-970d-01d3737a47d7
-- title:
--   Proof of Proposition 2.4, p. 13 (retired agent) — at y* meeting the retired budget, the dual value equals the objective of (c*, H*)
-- statement:
--   Retired-agent case ($R_0=1$) of the equality chain in the proof of Proposition 2.4 (the paper treats $R_t=0$ "without loss of generality"; this is the other case, posed at $t=0$).
--
--   Assume the set-up of §2.1, Assumption 2.1, a continuous positive version $\mathcal Z$ of the projected density (6), Assumption 2.2 for $U_1$ and $U_2$, Assumption 2.3 at $t=0$, and integrability of the dual. Let $x>0$ and $y^*>0$ satisfy the retired budget equation
--   $$\mathcal X_1(0,y^*)+\mathcal X_2(0,y^*)=\tilde E\Big[\int_0^T \frac{I_1(s,y^*_s)}{B_s}\,ds+\frac{I_2(T,y^*_T)}{B_T}\Big]=x,$$
--   where $y^*_s=y^*e^{\beta s}\mathcal Z_s/B_s$. Then, with $c^*_s=I_1(s,y^*_s)$ and $H^*=I_2(T,y^*_T)$,
--   $$\mathbf L(0,y^*,1)+y^*x=E\Big[\int_0^T e^{-\beta s}U_1(s,c^*_s)\,ds+e^{-\beta T}U_2(T,H^*)\Big],$$
--   the right side being the objective (12) of the retired agent (retirement time $0$, so the labour-cost term vanishes).
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), pp. 13–14, proof of Proposition 2.4 (case R_t = 1)

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market
import Definitions.Def_RetirePartialInfo_Duality_Utility
import Definitions.Def_RetirePartialInfo_Duality_Primal
import Definitions.Def_RetirePartialInfo_Duality_Dual

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace RetirePartialInfo.Duality

/-- **Proof of Proposition 2.4, the equality chain, retired agent** (`R_0 = 1`), p. 13 (Chen,
Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021),
pp. 13–14, proof of Proposition 2.4, the case `R_t = 1` covered by "without loss of generality"):
if `y* > 0` satisfies the retired budget equation `𝒳_1(0, y*) + 𝒳_2(0, y*) = x`, then
`𝐋(0, y*, 1) + y* x = E[∫_0^T e^{−βs} U_1(s, c*_s) ds + e^{−βT} U_2(T, H*)]`
with `c*_s = I_1(s, y*_s)`, `H* = I_2(T, y*_T)` (the objective (12) with `R ≡ 1`, i.e. retirement
time `0`). -/
theorem proof_2_4_value_eq_retired {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (hU1 : Assumption22 p U1) (hU2 : Assumption22 p U2)
    (h23 : Assumption23 p st Iθ Zv U1 U2) (hdual : DualIntegrable p st Zv U1 U2)
    (x : ℝ) (hx : 0 < x) (ystar : ℝ) (hystar : 0 < ystar)
    (h21eq : X12 p st Iθ Zv U1 U2 ystar = ENNReal.ofReal x) :
    L1 p st Zv U1 U2 ystar + ystar * x =
      Jobj p st U1 U2 (cstar p Zv U1 ystar) (Hstar p Zv U2 ystar) (fun _ => 0) := by sorry

end RetirePartialInfo.Duality
