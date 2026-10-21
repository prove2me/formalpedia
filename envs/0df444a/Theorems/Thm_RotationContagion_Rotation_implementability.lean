-- Prove2me | Theorems.Thm_RotationContagion_Rotation_implementability
-- name    : RotationContagion.Rotation.implementability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T16:21:36.766626+00:00
-- url     : https://prove2.me/theorems/fefd8054-a5b0-4a88-9562-20cf6e91f8ee
-- title:
--   Proof of Proposition 1, p. 11 — the two candidate distributions are implemented by rotation schedules
-- statement:
--   Assume $\gamma > 0$, $K > 1$, $R \ge 0$, and let $\mu$ be a probability measure on $[0,\infty)$, the law of the infection time. Then:
--
--   1. the frequent rotation $r(i,t) = 1/2$ and, for each $i$, the schedule $r(i,t) = 1$, $r(1-i,t) = 0$ are rotation schedules;
--   2. under the frequent rotation the exposure time is $R/2$ for every infected group and infection time, so its distribution is the point mass at $R/2$;
--   3. for every prevalence family of the frequent rotation, the expected terminal prevalence is
--   $$\mathrm E\, p^\omega_{t^*+R}(\omega) = \ell(R/2);$$
--   4. for every $i$ and every prevalence family of the schedule activating group $i$ throughout,
--   $$\mathrm E\, p^\omega_{t^*+R}(\omega) = \frac{\ell(0) + \ell(R)}{2}.$$
--
--   Parts 3 and 4 show that the solutions of (P2) are attained in (P1).
-- source:
--   Ely, Galeotti & Steiner, Rotation as Contagion Mitigation, working paper of 29 October 2020 (published Management Science 2021, doi:10.1287/mnsc.2020.3910), p. 11, proof of Proposition 1

import Mathlib
import Definitions.Def_RotationContagion_Rotation_Model

namespace RotationContagion.Rotation

open MeasureTheory

/-- Proof of Proposition 1, p. 11: the frequent rotation and the one-group schedules are
schedules; the frequent rotation gives exposure `R/2` for sure and expected terminal prevalence
`ℓ(R/2)`; activating one group throughout gives expected terminal prevalence
`(ℓ(0) + ℓ(R))/2`. -/
theorem implementability (P : Params) (hP : P.Standing) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : μ (Set.Iio 0) = 0) :
    IsSchedule freqSched ∧ (∀ i : Fin 2, IsSchedule (oneGroupSched i)) ∧
      (∀ (ω : Fin 2) (t0 : ℝ), exposure P freqSched ω t0 = P.R / 2) ∧
      (∀ p, IsPrevalenceFamily P freqSched p → expectedTerminal P μ p = loss P (P.R / 2)) ∧
      ∀ (i : Fin 2) (p : Fin 2 → ℝ → ℝ → ℝ), IsPrevalenceFamily P (oneGroupSched i) p →
        expectedTerminal P μ p = (loss P 0 + loss P P.R) / 2 := by sorry

end RotationContagion.Rotation
