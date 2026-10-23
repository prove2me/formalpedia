-- Prove2me | Theorems.Thm_RiskEU_OOSUVar_eq_IA55
-- name    : RiskEU.OOSUVar.eq_IA55
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-22T15:53:41.443022+00:00
-- url     : https://prove2.me/theorems/3879c993-25fc-4d06-9afc-c7bf2a24e6a1
-- title:
--   (IA55), p. IA37 — $\mathbb E[v_2^{-2}(1+y_1^2+y_2^2+s_1/w_1+a^2/v_2)]$
-- statement:
--   Let $z_2\sim\mathcal N(\sqrt T\psi,1)$, $u_0\sim\chi^2_{N-2}$, $v_2\sim\chi^2_{T-N+1}$, $w_1\sim\chi^2_{T-N+3}$, $w_2\sim\chi^2_{T-N+2}$, $s_1\sim\chi^2_{N-4}$, $s_2\sim\chi^2_{N-3}$ and $x_{11},x_{21},a,b,c\sim\mathcal N(0,1)$ be mutually independent (the auxiliary variables of Kan et al. (2022b, Proposition 1) as restated on pp. IA35–IA36, with footnote 6: $x_{11},x_{21}$ are set to $0$ when $N=2$, $c$ when $N\le 3$, and $\chi^2_0=\delta_0$), with $N\ge 2$, $T>N+7$, $\psi^2\ge0$, and let $y_1=\frac{x_{11}}{\sqrt{w_1}}+\frac{bx_{21}}{\sqrt{w_1w_2}}+\frac{ax_{21}}{\sqrt{v_2w_2}}$, $y_2=\frac{c}{\sqrt{w_1}}+\frac{b\sqrt{s_2}}{\sqrt{w_1w_2}}+\frac{a\sqrt{s_2}}{\sqrt{v_2w_2}}$ as in (IA45)–(IA46). Then the following random variable is integrable and
--
--   $$\mathbb E\left[\frac1{v_2^2}\left(1+y_1^2+y_2^2+\frac{s_1}{w_1}+\frac{a^2}{v_2}\right)\right]=\frac{(T-2)(T-N-4)}{(T-N)(T-N-1)(T-N-3)(T-N-5)}.\qquad\text{(IA55)}$$
--
--   This is one of the expectations entering the expansion (IA50).
--
--   **Formalization note.** The auxiliary variables are any family $X$ on a probability space $(\Omega',Q)$ satisfying `IsKanFamily N T psi2 Q X` (mutual independence and the laws `kanLaw`); $x_{21}$ enters through `KanVar.x21'` (footnote 6), $\psi=\sqrt{\psi^2}$ through `Real.sqrt psi2`, and Lean's conventions $1/0=0$, $\sqrt{x}=0$ for $x\le0$ only matter on null sets.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Internet Appendix, proof of Proposition 1, eq. (IA55), p. IA37

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_RiskEU_OOSUVar_KanRepresentation

namespace RiskEU.OOSUVar

open MeasureTheory ProbabilityTheory Matrix

theorem eq_IA55 {N T : ℕ} (hN : 2 ≤ N) (hT : N + 7 < T) (psi2 : ℝ) (hpsi2 : 0 ≤ psi2)
    {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (X : KanVar → Ω' → ℝ) (hX : IsKanFamily N T psi2 Q X) :
    Integrable (fun ω' => 1 / X .v2 ω' ^ 2 * (1 + KanVar.y1 N (fun i => X i ω') ^ 2 + KanVar.y2 N (fun i => X i ω') ^ 2 + X .s1 ω' / X .w1 ω' + X .a ω' ^ 2 / X .v2 ω')) Q ∧
    ∫ ω', 1 / X .v2 ω' ^ 2 * (1 + KanVar.y1 N (fun i => X i ω') ^ 2 + KanVar.y2 N (fun i => X i ω') ^ 2 + X .s1 ω' / X .w1 ω' + X .a ω' ^ 2 / X .v2 ω') ∂Q =
      ((T : ℝ) - 2) * ((T : ℝ) - N - 4) /
        (((T : ℝ) - N) * ((T : ℝ) - N - 1) * ((T : ℝ) - N - 3) * ((T : ℝ) - N - 5)) := by sorry

end RiskEU.OOSUVar
