-- Prove2me | Theorems.Thm_RiskEU_OOSUVar_eq_IA66
-- name    : RiskEU.OOSUVar.eq_IA66
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-22T15:53:36.735278+00:00
-- url     : https://prove2.me/theorems/f2a6ffb3-4f9b-4772-b7f6-1d84fa7a4fe1
-- title:
--   (IA66), p. IA38 — $\mathbb E[v_2^{-3}(1+(x_{21}^2+s_2)/w_2)]$
-- statement:
--   Let $z_2\sim\mathcal N(\sqrt T\psi,1)$, $u_0\sim\chi^2_{N-2}$, $v_2\sim\chi^2_{T-N+1}$, $w_1\sim\chi^2_{T-N+3}$, $w_2\sim\chi^2_{T-N+2}$, $s_1\sim\chi^2_{N-4}$, $s_2\sim\chi^2_{N-3}$ and $x_{11},x_{21},a,b,c\sim\mathcal N(0,1)$ be mutually independent (the auxiliary variables of Kan et al. (2022b, Proposition 1) as restated on pp. IA35–IA36, with footnote 6: $x_{11},x_{21}$ are set to $0$ when $N=2$, $c$ when $N\le 3$, and $\chi^2_0=\delta_0$), with $N\ge 2$, $T>N+7$, $\psi^2\ge0$, and let $y_1=\frac{x_{11}}{\sqrt{w_1}}+\frac{bx_{21}}{\sqrt{w_1w_2}}+\frac{ax_{21}}{\sqrt{v_2w_2}}$, $y_2=\frac{c}{\sqrt{w_1}}+\frac{b\sqrt{s_2}}{\sqrt{w_1w_2}}+\frac{a\sqrt{s_2}}{\sqrt{v_2w_2}}$ as in (IA45)–(IA46). Then the following random variable is integrable and
--
--   $$\mathbb E\left[\frac1{v_2^3}\left(1+\frac{x_{21}^2+s_2}{w_2}\right)\right]=\frac{T-2}{(T-N)(T-N-1)(T-N-3)(T-N-5)}.\qquad\text{(IA66)}$$
--
--   This is one of the expectations entering the expansion (IA61).
--
--   **Formalization note.** The auxiliary variables are any family $X$ on a probability space $(\Omega',Q)$ satisfying `IsKanFamily N T psi2 Q X` (mutual independence and the laws `kanLaw`); $x_{21}$ enters through `KanVar.x21'` (footnote 6), $\psi=\sqrt{\psi^2}$ through `Real.sqrt psi2`, and Lean's conventions $1/0=0$, $\sqrt{x}=0$ for $x\le0$ only matter on null sets.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Internet Appendix, proof of Proposition 1, eq. (IA66), p. IA38

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_RiskEU_OOSUVar_KanRepresentation

namespace RiskEU.OOSUVar

open MeasureTheory ProbabilityTheory Matrix

theorem eq_IA66 {N T : ℕ} (hN : 2 ≤ N) (hT : N + 7 < T) (psi2 : ℝ) (hpsi2 : 0 ≤ psi2)
    {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (X : KanVar → Ω' → ℝ) (hX : IsKanFamily N T psi2 Q X) :
    Integrable (fun ω' => 1 / X .v2 ω' ^ 3 * (1 + (KanVar.x21' N (fun i => X i ω') ^ 2 + X .s2 ω') / X .w2 ω')) Q ∧
    ∫ ω', 1 / X .v2 ω' ^ 3 * (1 + (KanVar.x21' N (fun i => X i ω') ^ 2 + X .s2 ω') / X .w2 ω') ∂Q =
      ((T : ℝ) - 2) / (((T : ℝ) - N) * ((T : ℝ) - N - 1) * ((T : ℝ) - N - 3) * ((T : ℝ) - N - 5)) := by sorry

end RiskEU.OOSUVar
