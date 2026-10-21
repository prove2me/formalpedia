-- Prove2me | Theorems.Thm_RetirePartialInfo_Duality_eq_13
-- name    : RetirePartialInfo.Duality.eq_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:38.355772+00:00
-- url     : https://prove2.me/theorems/1750f9bb-722d-4e1e-aacb-601b73c29fb7
-- title:
--   (13), p. 11 — after retirement, J₁(c, H) ≤ 𝐋(0, y, 1) + yx for every (c, H) ∈ ℬ₁(x) and y > 0
-- statement:
--   Work under the standing hypotheses of the mission (the set-up of §2.1, the Itô integral defining $Z$, Assumption 2.1, a continuous positive version of $\mathcal Z$, Assumption 2.2 for $U_1$ and $U_2$) and assume the dual integrability condition. Let $x\in\mathbb R$, $y>0$ and $(c,H)\in\mathcal B_1(x)$. Then
--   $$\mathbb E\Bigl[\int_0^Te^{-\beta s}U_1(s,c_s)\,ds+e^{-\beta T}U_2(T,H_T)\Bigr]\le\mathbf L(0,y,1)+yx.$$
--   Equivalently, $V(0,x,1)-yx\le\mathbf L(0,y,1)$ whenever $\mathcal B_1(x)\neq\emptyset$.
--
--   This is weak duality for the retired agent: every multiplier $y>0$ gives an upper bound on the value.
--
--   **Formalization Note.** Posed for each plan rather than for the supremum, so no supremum over a possibly empty set is involved; at $t=0$.
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), p. 11, (13)

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market
import Definitions.Def_RetirePartialInfo_Duality_Utility
import Definitions.Def_RetirePartialInfo_Duality_Primal
import Definitions.Def_RetirePartialInfo_Duality_Dual

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace RetirePartialInfo.Duality

/-- **(13)**, p. 11 (Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), p. 11, (13)): weak duality after retirement, at `t = 0`. "For any
`y > 0`, (8) implies that `V(t, x_t, 1) − yx_t ≤ … ≤ E_t[∫_t^T e^{−β(s−t)}Ũ_1(s, y_s)ds +
e^{−β(T−t)}Ũ_2(T, y_T)] := 𝐋(t, y, 1)`."

For every initial wealth `x`, every multiplier `y > 0` and every plan `(c, H) ∈ ℬ_1(x)`,
`E[∫_0^T e^{−βs} U_1(s, c_s) ds + e^{−βT} U_2(T, H_T)] ≤ 𝐋(0, y, 1) + y x`.

**Formalization Note.** Posed plan by plan (equivalently `V(0, x, 1) − yx ≤ 𝐋(0, y, 1)` when
`ℬ_1(x) ≠ ∅`), so no supremum over a possibly empty set is involved. The standing hypotheses are: the set-up of §2.1 (`Setting.Standing`); `Iθ` is the Itô integral
`∫_0^· θ dW` (`IsItoIntegral`), which defines `Z` (3); Assumption 2.1; `Zv` is a continuous
positive version of the projected density `𝒵_t = E[Z_T | F^S_t]` (6) (`IsZVersion`); Assumption 2.2
for `U_1` and `U_2`; and the
integrability of the dual (`DualIntegrable`, added: the paper treats `𝐋` as a finite real). -/
theorem eq_13 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (hU1 : Assumption22 p U1) (hU2 : Assumption22 p U2)
    (hdual : DualIntegrable p st Zv U1 U2) (x y : ℝ) (hy : 0 < y)
    (q : (ℝ≥0 → Ω → ℝ) × (ℝ≥0 → Ω → ℝ)) (hq : q ∈ B1class p st Iθ U1 U2 x) :
    J1 p st U1 U2 q ≤ L1 p st Zv U1 U2 y + y * x := by sorry

end RetirePartialInfo.Duality
