-- Prove2me | Theorems.Thm_RiskEU_OOSUVar_eq_IA57
-- name    : RiskEU.OOSUVar.eq_IA57
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T08:06:49.335571+00:00
-- url     : https://prove2.me/theorems/f19708fa-1dc8-48da-acec-0b558da5e662
-- title:
--   (IA57), p. IA37 — E[(1/v₂⁴)(1 + (x₂₁² + s₂)/w₂)²] for the Kan et al. auxiliary variables
-- statement:
--   Let $N\ge2$, $T>N+7$ and $\psi^2\ge0$, and let $z_2,u_0,v_2,w_1,w_2,s_1,s_2,x_{11},x_{21},a,b,c$ be mutually independent with the laws of Kan et al. (2022b, Proposition 1) (see `KanRepresentation`), with $x_{21}$ replaced by $0$ when $N=2$ (footnote 6). Then the quantity below is integrable and
--
--   $$\mathbb E\Big[\frac{1}{v_2^4}\Big(1+\frac{x_{21}^2+s_2}{w_2}\Big)^2\Big]=\frac{(T-2)(T-4)}{(T-N)(T-N-1)(T-N-2)(T-N-3)(T-N-5)(T-N-7)}.$$
--
--   This is the factor of the $\kappa^4$ term in (IA50). Since $v_2\sim\chi^2_{T-N+1}$, the fourth negative moment of $v_2$ is finite exactly when $T>N+7$, which is where Assumption 1's bound is used.
--
--   **Formalization Note.** The hypothesis $\psi^2\ge0$ only fixes the law of $z_2$, which does not appear in this identity.
-- source:
--   Lassance, Martín-Utrera, Simaan, The Risk of Expected Utility under Parameter Uncertainty, SSRN 3855546 (version dated August 18, 2023), Section IA.10, proof of Proposition 1, (IA57), p. IA37

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Definitions.Def_RiskEU_OOSUVar_KanRepresentation

namespace RiskEU.OOSUVar

open MeasureTheory ProbabilityTheory Matrix

theorem eq_IA57 {N T : ℕ} (hN : 2 ≤ N) (hT : N + 7 < T) (psi2 : ℝ) (hpsi2 : 0 ≤ psi2)
    {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω') [IsProbabilityMeasure Q]
    (X : KanVar → Ω' → ℝ) (hX : IsKanFamily N T psi2 Q X) :
    Integrable (fun ω' => 1 / X .v2 ω' ^ 4 *
        (1 + (KanVar.x21' N (fun i => X i ω') ^ 2 + X .s2 ω') / X .w2 ω') ^ 2) Q ∧
    ∫ ω', 1 / X .v2 ω' ^ 4 *
        (1 + (KanVar.x21' N (fun i => X i ω') ^ 2 + X .s2 ω') / X .w2 ω') ^ 2 ∂Q =
      ((T : ℝ) - 2) * ((T : ℝ) - 4) /
        (((T : ℝ) - N) * ((T : ℝ) - N - 1) * ((T : ℝ) - N - 2) * ((T : ℝ) - N - 3) *
          ((T : ℝ) - N - 5) * ((T : ℝ) - N - 7)) := by sorry

end RiskEU.OOSUVar
