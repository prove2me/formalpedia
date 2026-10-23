-- Prove2me | Theorems.Thm_RiskEU_OOSUVar_eq_IA63
-- name    : RiskEU.OOSUVar.eq_IA63
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-22T15:53:36.326206+00:00
-- url     : https://prove2.me/theorems/840e1a54-2760-41b0-9b40-93f95ba0cd60
-- title:
--   (IA63), p. IA38 — $\mathbb E[z_2(z_2^2+u_0)]$
-- statement:
--   Let $z_2\sim\mathcal N(\sqrt T\psi,1)$, $u_0\sim\chi^2_{N-2}$, $v_2\sim\chi^2_{T-N+1}$, $w_1\sim\chi^2_{T-N+3}$, $w_2\sim\chi^2_{T-N+2}$, $s_1\sim\chi^2_{N-4}$, $s_2\sim\chi^2_{N-3}$ and $x_{11},x_{21},a,b,c\sim\mathcal N(0,1)$ be mutually independent (the auxiliary variables of Kan et al. (2022b, Proposition 1) as restated on pp. IA35–IA36, with footnote 6: $x_{11},x_{21}$ are set to $0$ when $N=2$, $c$ when $N\le 3$, and $\chi^2_0=\delta_0$), with $N\ge 2$, $T>N+7$, $\psi^2\ge0$, and let $y_1=\frac{x_{11}}{\sqrt{w_1}}+\frac{bx_{21}}{\sqrt{w_1w_2}}+\frac{ax_{21}}{\sqrt{v_2w_2}}$, $y_2=\frac{c}{\sqrt{w_1}}+\frac{b\sqrt{s_2}}{\sqrt{w_1w_2}}+\frac{a\sqrt{s_2}}{\sqrt{v_2w_2}}$ as in (IA45)–(IA46). Then $z_2(z_2^2+u_0)$ is integrable and
--
--   $$\mathbb E\big[z_2(z_2^2+u_0)\big]=\sqrt T\psi\,(N+1+T\psi^2).\qquad\text{(IA63)}$$
--
--   This is one of the expectations entering the expansion (IA61); here $\psi=\sqrt{\psi^2}$.
--
--   **Formalization note.** The auxiliary variables are any family $X$ on a probability space $(\Omega',Q)$ satisfying `IsKanFamily N T psi2 Q X` (mutual independence and the laws `kanLaw`); $x_{21}$ enters through `KanVar.x21'` (footnote 6), $\psi=\sqrt{\psi^2}$ through `Real.sqrt psi2`, and Lean's conventions $1/0=0$, $\sqrt{x}=0$ for $x\le0$ only matter on null sets.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Internet Appendix, proof of Proposition 1, eq. (IA63), p. IA38

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_RiskEU_OOSUVar_KanRepresentation

namespace RiskEU.OOSUVar

open MeasureTheory ProbabilityTheory Matrix

theorem eq_IA63 {N T : ℕ} (hN : 2 ≤ N) (hT : N + 7 < T) (psi2 : ℝ) (hpsi2 : 0 ≤ psi2)
    {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (X : KanVar → Ω' → ℝ) (hX : IsKanFamily N T psi2 Q X) :
    Integrable (fun ω' => X .z2 ω' * (X .z2 ω' ^ 2 + X .u0 ω')) Q ∧
    ∫ ω', X .z2 ω' * (X .z2 ω' ^ 2 + X .u0 ω') ∂Q =
      Real.sqrt T * Real.sqrt psi2 * ((N : ℝ) + 1 + T * psi2) := by sorry

end RiskEU.OOSUVar
