-- Prove2me | Theorems.Thm_RotationContagion_Rotation_symmetrization
-- name    : RotationContagion.Rotation.symmetrization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:37.179998+00:00
-- url     : https://prove2.me/theorems/fcf70630-97eb-4335-92d8-2105fe4760e6
-- title:
--   p. 8 — τ⁰ + τ¹ = R and E ℓ(τ) = ½ E[ℓ(τ) + ℓ(R − τ)]
-- statement:
--   Assume $\gamma > 0$, $K > 1$, $R \ge 0$, let $\mu$ be a probability measure on $[0,\infty)$ (the law of $t^*$), $\omega$ uniform on $\{0,1\}$ and independent of $t^*$, and $r$ a rotation schedule. Write $\tau^i = \int_{t^*}^{t^*+R} r(i,t)\,dt$. Then
--
--   1. $\tau^0 + \tau^1 = R$ for every infection time $t^* \ge 0$;
--   2. the expected loss equals the expected symmetrized loss:
--   $$\mathrm E\,\ell(\tau) = \tfrac12\,\mathrm E\big[\ell(\tau) + \ell(R-\tau)\big],$$
--   where $\tau = \tau^\omega$ and the expectation is over $t^*$ and $\omega$.
--
--   Part 2 is the identity that motivates the relaxed rotation problem (P2), whose objective is $\ell(\tau) + \ell(R-\tau)$.
-- source:
--   Ely, Galeotti & Steiner, Rotation as Contagion Mitigation, working paper of 29 October 2020 (published Management Science 2021, doi:10.1287/mnsc.2020.3910), p. 8, proof of Lemma 2 and the display before (P2)

import Mathlib
import Definitions.Def_RotationContagion_Rotation_Model

namespace RotationContagion.Rotation

open MeasureTheory

/-- p. 8 (proof of Lemma 2 and the display before (P2)): the exposure times of the two groups sum
to `R`, and `E ℓ(τ) = (1/2) E[ℓ(τ) + ℓ(R - τ)]`. -/
theorem symmetrization (P : Params) (hP : P.Standing) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) (r : Fin 2 → ℝ → ℝ) (hr : IsSchedule r) :
    (∀ t0 : ℝ, 0 ≤ t0 → exposure P r 0 t0 + exposure P r 1 t0 = P.R) ∧
      (1 / 2 : ℝ) * ∑ ω : Fin 2, ∫ t0, loss P (exposure P r ω t0) ∂μ =
        (1 / 2 : ℝ) * ∑ ω : Fin 2,
          ∫ t0, (1 / 2 : ℝ) * (loss P (exposure P r ω t0) + loss P (P.R - exposure P r ω t0)) ∂μ := by sorry

end RotationContagion.Rotation
