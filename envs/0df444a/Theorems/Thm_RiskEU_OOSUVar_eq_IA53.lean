-- Prove2me | Theorems.Thm_RiskEU_OOSUVar_eq_IA53
-- name    : RiskEU.OOSUVar.eq_IA53
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:43.531408+00:00
-- url     : https://prove2.me/theorems/a5812dbb-4cc4-422a-b23b-7f814a28599a
-- title:
--   (IA53), p. IA37 — E[(1 + y₁² + y₂² + s₁/w₁ + a²/v₂)²] for the Kan et al. auxiliary variables
-- statement:
--   Let $N\ge2$, $T>N+7$ and $\psi^2\ge0$, and let $z_2,u_0,v_2,w_1,w_2,s_1,s_2,x_{11},x_{21},a,b,c$ be mutually independent with the laws of Kan et al. (2022b, Proposition 1) (see `KanRepresentation`), with $y_1,y_2$ as in (IA45)–(IA46) under footnote 6's convention. Then the square below is integrable and
--
--   $$\mathbb E\Big[\Big(1+y_1^2+y_2^2+\frac{s_1}{w_1}+\frac{a^2}{v_2}\Big)^2\Big]=\frac{(T-2)(T-4)}{(T-N-1)(T-N-3)}.$$
--
--   This is the coefficient of $\sigma_g^4$ in the second moment (IA50) of the out-of-sample return variance.
--
--   **Formalization Note.** The hypothesis $\psi^2\ge0$ only fixes the law $\mathcal N(\sqrt T\psi,1)$ of $z_2$, which does not appear in this identity; it is part of the setting in which the page states the representation.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Section IA.10, proof of Proposition 1, (IA53), p. IA37

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_RiskEU_OOSUVar_KanRepresentation

namespace RiskEU.OOSUVar

open MeasureTheory ProbabilityTheory Matrix

theorem eq_IA53 {N T : ℕ} (hN : 2 ≤ N) (hT : N + 7 < T) (psi2 : ℝ) (hpsi2 : 0 ≤ psi2)
    {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (X : KanVar → Ω' → ℝ) (hX : IsKanFamily N T psi2 Q X) :
    Integrable (fun ω' => (1 + KanVar.y1 N (fun i => X i ω') ^ 2 + KanVar.y2 N (fun i => X i ω') ^ 2 +
        X .s1 ω' / X .w1 ω' + X .a ω' ^ 2 / X .v2 ω') ^ 2) Q ∧
    ∫ ω', (1 + KanVar.y1 N (fun i => X i ω') ^ 2 + KanVar.y2 N (fun i => X i ω') ^ 2 +
        X .s1 ω' / X .w1 ω' + X .a ω' ^ 2 / X .v2 ω') ^ 2 ∂Q =
      ((T : ℝ) - 2) * ((T : ℝ) - 4) / (((T : ℝ) - N - 1) * ((T : ℝ) - N - 3)) := by sorry

end RiskEU.OOSUVar
