-- Prove2me | Theorems.Thm_StochIneqPO_DBar_dbar_attained
-- name    : StochIneqPO.DBar.dbar_attained
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:29.411989+00:00
-- url     : https://prove2.me/theorems/b35c47fc-2009-4c2f-9c94-7593d0dd9f59
-- title:
--   Proof of Theorem 8 — stationary coupling attains d̄
-- statement:
--   Let $P,Q$ be stationary laws of real-valued two-sided processes, with integrable time-zero coordinates. There exists a stationary coupling $\nu$ of $P,Q$ that attains the defining infimum:
--
--   $$\bar d(P,Q)=\int|\omega_1^0-\omega_2^0|\,\nu(d\omega_1,d\omega_2).$$
--
--   This is the attainment claim stated in the proof of Theorem 8. It makes the lower-law construction applicable to an optimal coupling.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), proof of Theorem 8, pp. 910–911 (PDF pp. 12–13), attainment display

import Mathlib
import Definitions.Def_StochIneqPO_DBar_IsShiftInvariant
import Definitions.Def_StochIneqPO_DBar_dbar

namespace StochIneqPO.DBar

open MeasureTheory

/-- The attainment display in the proof of Theorem 8, pp. 910–911. -/
theorem dbar_attained
    (P Q : Measure (ℤ → ℝ))
    (hP : IsShiftInvariant P) (hQ : IsShiftInvariant Q)
    (hPi : Integrable (fun ω : ℤ → ℝ => ω 0) P)
    (hQi : Integrable (fun ω : ℤ → ℝ => ω 0) Q) :
    ∃ ν : Measure ((ℤ → ℝ) × (ℤ → ℝ)),
      IsPairShiftInvariant ν ∧ ν.map Prod.fst = P ∧ ν.map Prod.snd = Q ∧
      dbar P Q = ∫ z, |z.1 0 - z.2 0| ∂ν := by sorry

end StochIneqPO.DBar
