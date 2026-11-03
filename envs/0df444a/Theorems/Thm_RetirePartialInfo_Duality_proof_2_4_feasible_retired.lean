-- Prove2me | Theorems.Thm_RetirePartialInfo_Duality_proof_2_4_feasible_retired
-- name    : RetirePartialInfo.Duality.proof_2_4_feasible_retired
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T05:40:27.930244+00:00
-- url     : https://prove2.me/theorems/ea7af8f1-36ba-46e9-ad1f-1e0acc91723d
-- title:
--   Proof of Proposition 2.4, pp. 13–14 (retired agent) — under the retired budget equation, (c*, H*) is feasible: (c*, H) ∈ ℬ₁(x)
-- statement:
--   Retired-agent case ($R_0=1$) of the feasibility step in the proof of Proposition 2.4, posed at $t=0$.
--
--   Assume the set-up of §2.1, Assumption 2.1, a continuous positive version $\mathcal Z$ of the projected density (6), Assumption 2.2 for $U_1$ and $U_2$, Assumption 2.3 at $t=0$, and integrability of the dual. Let $x>0$ and $y^*>0$ satisfy $\mathcal X_1(0,y^*)+\mathcal X_2(0,y^*)=x$. Then there is a wealth process $H$ with terminal value $H_T=H^*=I_2(T,y^*_T)$ such that the pair $(c^*,H)$, $c^*_s=I_1(s,y^*_s)$, belongs to $\mathcal B_1(x)$: it is admissible with retirement at time $0$, starts from $H_0=x$, satisfies the budget constraint (8), and has $H_T>0$ and an integrable objective.
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

/-- **Proof of Proposition 2.4, feasibility, retired agent** (`R_0 = 1`), pp. 13–14 (Chen, Jeon,
Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021),
pp. 13–14, proof of Proposition 2.4, the case `R_t = 1`): if `y* > 0` satisfies
`𝒳_1(0, y*) + 𝒳_2(0, y*) = x`, there is a wealth process `H` with `H_T = I_2(T, y*_T)` such that
`(c*, H) ∈ ℬ_1(x)`, `c*_s = I_1(s, y*_s)`. -/
theorem proof_2_4_feasible_retired {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (hU1 : Assumption22 p U1) (hU2 : Assumption22 p U2)
    (h23 : Assumption23 p st Iθ Zv U1 U2) (hdual : DualIntegrable p st Zv U1 U2)
    (x : ℝ) (hx : 0 < x) (ystar : ℝ) (hystar : 0 < ystar)
    (h21eq : X12 p st Iθ Zv U1 U2 ystar = ENNReal.ofReal x) :
    ∃ H : ℝ≥0 → Ω → ℝ, (∀ ω, H p.Tn ω = Hstar p Zv U2 ystar ω) ∧
      (cstar p Zv U1 ystar, H) ∈ B1class p st Iθ U1 U2 x := by sorry

end RetirePartialInfo.Duality
