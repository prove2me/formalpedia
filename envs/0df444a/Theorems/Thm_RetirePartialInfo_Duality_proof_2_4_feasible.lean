-- Prove2me | Theorems.Thm_RetirePartialInfo_Duality_proof_2_4_feasible
-- name    : RetirePartialInfo.Duality.proof_2_4_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:34.984738+00:00
-- url     : https://prove2.me/theorems/0cb64f64-7b0d-4858-8689-e4760073b6b9
-- title:
--   Proof of Proposition 2.4, p. 14 — under (21) the candidate (c*, H*, R*) belongs to ℬ(x)
-- statement:
--   Work under the standing hypotheses of the mission, Assumption 2.3 at $t=0$ and the dual integrability condition. Let $x>b(0)$, $y^*>0$ and let $\hat\tau$ be an $\mathcal F^S$-stopping time in $[0,T_1]$ with
--   $$\mathcal X(0,y^*)=x-b(0)\qquad(21),$$
--   where $\mathcal X$ is built from $c^*_s=I_1(s,y^*_s)$, $H^*=I_2(T,y^*_T)$ and $R^*_s=\mathbf 1\{s\ge\hat\tau\}$. Then there is an $\mathcal F^S$-adapted wealth process $H$ with terminal value $H_T=H^*$ such that
--   $$(c^*,H,R^*)\in\mathcal B(x).$$
--
--   This is the feasibility half of "By Proposition 2.3, the triplet $(c^*,H^*,R^*)$ is the optimal solution to the primal problem" (p. 14): the candidate built from the dual solution satisfies the budget constraint (8) with initial wealth $x$.
--
--   **Formalization Note.** At $t=0$, $R_0=0$. Optimality of $\hat\tau$ in (14) is not needed here and is not assumed.
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), p. 14, proof of Proposition 2.4

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market
import Definitions.Def_RetirePartialInfo_Duality_Utility
import Definitions.Def_RetirePartialInfo_Duality_Primal
import Definitions.Def_RetirePartialInfo_Duality_Dual

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace RetirePartialInfo.Duality

/-- **Proof of Proposition 2.4, feasibility of the candidate**, p. 14 (Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), p. 14, proof of
Proposition 2.4): "By Proposition 2.3, the triplet `(c*, H*, R*)` is the optimal solution to the
primal problem"; the feasibility half: if `y* > 0` and a retirement time `τ̂` satisfy (21),
`𝒳(0, y*) = x − b(0)`, then there is an `F^S`-adapted wealth process `H` with terminal value
`H_T = H* = I_2(T, y*_T)` such that `(c*, H, R*) ∈ ℬ(x)`, where `c*_s = I_1(s, y*_s)` and
`R*_s = 1{s ≥ τ̂}`.

**Formalization Note.** At `t = 0`, `R_0 = 0`. The optimality of `τ̂` in (14) is not needed for
feasibility and is not assumed. The standing hypotheses are: the set-up of §2.1 (`Setting.Standing`); `Iθ` is the Itô integral
`∫_0^· θ dW` (`IsItoIntegral`), which defines `Z` (3); Assumption 2.1; `Zv` is a continuous
positive version of the projected density `𝒵_t = E[Z_T | F^S_t]` (6) (`IsZVersion`); Assumption 2.2
for `U_1` and `U_2`; Assumption 2.3 at `t = 0`; and `DualIntegrable`
(added). -/
theorem proof_2_4_feasible {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (hU1 : Assumption22 p U1) (hU2 : Assumption22 p U2)
    (h23 : Assumption23 p st Iθ Zv U1 U2) (hdual : DualIntegrable p st Zv U1 U2)
    (x : ℝ) (hx : b p 0 < x) (ystar : ℝ) (hystar : 0 < ystar)
    (τhat : Ω → ℝ≥0) (hτhat : IsRetirementTime p st τhat)
    (h21eq : Xcal p st Iθ Zv U1 U2 ystar τhat = ENNReal.ofReal (x - b p 0)) :
    ∃ H : ℝ≥0 → Ω → ℝ, (∀ ω, H p.Tn ω = Hstar p Zv U2 ystar ω) ∧
      (⟨cstar p Zv U1 ystar, H, τhat⟩ : Plan Ω) ∈ Bclass p st Iθ U1 U2 x := by sorry

end RetirePartialInfo.Duality
