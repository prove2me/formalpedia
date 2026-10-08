-- Prove2me | Theorems.Thm_StochIneqPO_DBar_meet_pushforward_le
-- name    : StochIneqPO.DBar.meet_pushforward_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:09.750446+00:00
-- url     : https://prove2.me/theorems/c70bbd00-0de8-4959-a2ee-19a9845670b6
-- title:
--   Proof of Theorem 8 — the meet law is a stationary common lower law
-- statement:
--   Let $\nu$ be a stationary probability law on pairs of real-valued two-sided paths, with marginals $P,Q$. Push $\nu$ forward by the coordinatewise minimum $\varphi$. The resulting law $R'=\nu\circ\varphi^{-1}$ is stationary and lies below each marginal in stochastic order:
--
--   $$R'\in\mathcal S_T,\qquad R'\prec P,\qquad R'\prec Q.$$
--
--   This is the common lower law constructed in the proof of Theorem 8.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), proof of Theorem 8, p. 911 (PDF p. 13), paragraph defining R′

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Definitions.Def_StochIneqPO_DBar_IsShiftInvariant
import Definitions.Def_StochIneqPO_DBar_IsPairShiftInvariant
import Definitions.Def_StochIneqPO_DBar_meetPath

namespace StochIneqPO.DBar

open MeasureTheory

/-- The meet pushforward in the proof of Theorem 8, p. 911. -/
theorem meet_pushforward_le
    (P Q : Measure (ℤ → ℝ))
    (ν : Measure ((ℤ → ℝ) × (ℤ → ℝ)))
    (hν : IsPairShiftInvariant ν)
    (hνP : ν.map Prod.fst = P) (hνQ : ν.map Prod.snd = Q) :
    IsShiftInvariant (ν.map meetPath) ∧
      StochIneqPO.Comparison.StochLE (ν.map meetPath) P ∧ StochIneqPO.Comparison.StochLE (ν.map meetPath) Q := by sorry

end StochIneqPO.DBar
