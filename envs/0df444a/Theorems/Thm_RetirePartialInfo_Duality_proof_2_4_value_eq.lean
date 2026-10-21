-- Prove2me | Theorems.Thm_RetirePartialInfo_Duality_proof_2_4_value_eq
-- name    : RetirePartialInfo.Duality.proof_2_4_value_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:00.931841+00:00
-- url     : https://prove2.me/theorems/ce4b6561-a3d6-4ef6-b7fa-bab9a4ec97ac
-- title:
--   Proof of Proposition 2.4, p. 13 — at (y*, τ̂) the dual value 𝐋(0, y*, 0) + y*(x − b(0)) equals the candidate's objective
-- statement:
--   Work under the standing hypotheses of the mission, Assumption 2.3 at $t=0$ and the dual integrability condition. Let $x>b(0)$ and $y^*>0$, and let $\hat\tau$ be an $\mathcal F^S$-stopping time in $[0,T_1]$ that is optimal in (14) at $y^*$ and satisfies (21) at $t=0$:
--   $$\mathcal X(0,y^*)=x-b(0),$$
--   with $\mathcal X$ computed from $c^*_s=I_1(s,y^*_s)$, $H^*=I_2(T,y^*_T)$ and $R^*_s=\mathbf 1\{s\ge\hat\tau\}$. Then
--   $$\mathbf L(0,y^*,0)+y^*\bigl(x-b(0)\bigr)=\mathbb E\Bigl[\int_0^Te^{-\beta s}\bigl(U_1(s,c^*_s)-\ell(1-R^*_s)\bigr)ds+e^{-\beta T}U_2(T,H^*)\Bigr].$$
--
--   This is the equality chain in the proof of Proposition 2.4: at the multiplier $y^*$ the dual value is the primal objective of the candidate (18).
--
--   **Formalization Note.** At $t=0$, $R_0=0$. $\hat\tau$ is any optimal stopping time of (14) at $y^*$, in place of the paper's hitting time $\hat\tau_{0,y^*}$, which is one.
-- source:
--   Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), p. 13, proof of Proposition 2.4

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market
import Definitions.Def_RetirePartialInfo_Duality_Utility
import Definitions.Def_RetirePartialInfo_Duality_Primal
import Definitions.Def_RetirePartialInfo_Duality_Dual

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace RetirePartialInfo.Duality

/-- **Proof of Proposition 2.4, the equality chain**, p. 13 (Chen, Jeon, Wong, Optimal retirement under partial information, SSRN 3683553 (version of June 8, 2021), p. 13, proof of
Proposition 2.4): with `R_t = 0`, if `τ̂` is optimal in (14) at `y*` and `y*` satisfies (21), the
dual value at `y*` equals the primal objective of the candidate (18):
`𝐋(0, y*, 0) + y*(x − b(0)) = E[∫_0^T e^{−βs}(U_1(s, c*_s) − ℓ(1 − R*_s)) ds + e^{−βT} U_2(T, H*)]`,
with `c*_s = I_1(s, y*_s)`, `H* = I_2(T, y*_T)`, `R*_s = 1{s ≥ τ̂}`.

**Formalization Note.** At `t = 0`. `τ̂` is any `F^S`-stopping time in `[0, T1]` that attains the
supremum (14) at `y*` (`IsOptimalStop`); the paper's hitting time `τ̂_{0,y*}` is one. (21) at `t = 0`,
`R_0 = 0` reads `𝒳(0, y*) = x − b(0)`, with `𝒳` computed in `[0, ∞]` (`Xcal`). The standing hypotheses are: the set-up of §2.1 (`Setting.Standing`); `Iθ` is the Itô integral
`∫_0^· θ dW` (`IsItoIntegral`), which defines `Z` (3); Assumption 2.1; `Zv` is a continuous
positive version of the projected density `𝒵_t = E[Z_T | F^S_t]` (6) (`IsZVersion`); Assumption 2.2
for `U_1` and `U_2`;
Assumption 2.3 at `t = 0`; and `DualIntegrable` (added). -/
theorem proof_2_4_value_eq {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (Iθ Zv : ℝ≥0 → Ω → ℝ) (U1 U2 : ℝ → ℝ → ℝ)
    (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ) (h21 : Assumption21 p st Iθ)
    (hZv : IsZVersion p st Iθ Zv) (hU1 : Assumption22 p U1) (hU2 : Assumption22 p U2)
    (h23 : Assumption23 p st Iθ Zv U1 U2) (hdual : DualIntegrable p st Zv U1 U2)
    (x : ℝ) (hx : b p 0 < x) (ystar : ℝ) (hystar : 0 < ystar)
    (τhat : Ω → ℝ≥0) (hτhat : IsRetirementTime p st τhat)
    (hopt : IsOptimalStop p st Zv U1 U2 ystar τhat hτhat)
    (h21eq : Xcal p st Iθ Zv U1 U2 ystar τhat = ENNReal.ofReal (x - b p 0)) :
    L0 p st Zv U1 U2 ystar + ystar * (x - b p 0) =
      Jobj p st U1 U2 (cstar p Zv U1 ystar) (Hstar p Zv U2 ystar) τhat := by sorry

end RetirePartialInfo.Duality
