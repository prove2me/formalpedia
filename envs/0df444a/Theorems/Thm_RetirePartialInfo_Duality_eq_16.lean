-- Prove2me | Theorems.Thm_RetirePartialInfo_Duality_eq_16
-- name    : RetirePartialInfo.Duality.eq_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:49.076658+00:00
-- url     : https://prove2.me/theorems/071f4ef9-faae-48d1-af6d-26326246b6e7
-- title:
--   (14) and (16), p. 12 — J(c, H, R) ≤ 𝐋(0, y, 0) + y(x − b(0)) for every (c, H, R) ∈ ℬ(x) and y > 0
-- statement:
--   Work under the standing hypotheses of the mission and assume the dual integrability condition. Let $x\in\mathbb R$, $y>0$ and $(c,H,R)\in\mathcal B(x)$. Then
--   $$\mathbb E\Bigl[\int_0^Te^{-\beta t}\bigl(U_1(t,c_t)-\ell(1-R_t)\bigr)dt+e^{-\beta T}U_2(T,H_T)\Bigr]\le\mathbf L(0,y,0)+y\bigl(x-b(0)\bigr),$$
--   where $\mathbf L(0,y,0)$ is the supremum (14) over all $\mathcal F^S$-stopping times $\tau\in[0,T_1]$.
--
--   Together with (13) this is the paper's (16), $V(t,x_t,R_t)\le\min_{y>0}\mathbf L(t,y,R_t)+y(x_t-b(t)(1-R_t))$, at $t=0$ for the working agent: weak duality with the retirement option.
--
--   **Formalization Note.** Posed for each plan, at $t=0$. The class $\mathcal B(x)$ contains every retirement time in $[0,T_1]$, including $\tau=0$; the case $R_t=1$ of (16) is the milestone (13).
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), p. 12, (14) and (16)

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market
import Definitions.Def_RetirePartialInfo_Duality_Utility
import Definitions.Def_RetirePartialInfo_Duality_Primal
import Definitions.Def_RetirePartialInfo_Duality_Dual

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace RetirePartialInfo.Duality

/-- **(14) and (16)**, p. 12 (Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), p. 12, (14) and (16)): weak duality with the retirement
option, at `t = 0`, `R_0 = 0`. "It is obvious from the above calculation that
`V(t, x_t, R_t) ≤ min_{y>0} 𝐋(t, y, R_t) + y(x_t − b(t)(1 − R_t))`."

For every initial wealth `x`, every multiplier `y > 0` and every plan `(c, H, R) ∈ ℬ(x)`,
`E[∫_0^T e^{−βt}(U_1(t, c_t) − ℓ(1 − R_t)) dt + e^{−βT} U_2(T, H_T)] ≤ 𝐋(0, y, 0) + y(x − b(0))`,
where `𝐋(0, y, 0)` is the supremum (14) over all `F^S`-stopping times `τ ∈ [0, T1]`.

**Formalization Note.** Posed plan by plan, at `t = 0` for the working agent (the class `ℬ(x)`
contains every retirement time `τ ∈ [0, T1]`, including `τ = 0`). The case `R_t = 1` of (16) is
`eq_13`. The standing hypotheses are: the set-up of §2.1 (`Setting.Standing`); `Iθ` is the Itô integral
`∫_0^· θ dW` (`IsItoIntegral`), which defines `Z` (3); Assumption 2.1; `Zv` is a continuous
positive version of the projected density `𝒵_t = E[Z_T | F^S_t]` (6) (`IsZVersion`); Assumption 2.2
for `U_1` and `U_2`; and `DualIntegrable` (added). -/
theorem eq_16 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (hU1 : Assumption22 p U1) (hU2 : Assumption22 p U2)
    (hdual : DualIntegrable p st Zv U1 U2) (x y : ℝ) (hy : 0 < y)
    (q : Plan Ω) (hq : q ∈ Bclass p st Iθ U1 U2 x) :
    J p st U1 U2 q ≤ L0 p st Zv U1 U2 y + y * (x - b p 0) := by sorry

end RetirePartialInfo.Duality
