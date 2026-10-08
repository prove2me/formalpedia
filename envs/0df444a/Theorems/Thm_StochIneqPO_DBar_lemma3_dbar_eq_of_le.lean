-- Prove2me | Theorems.Thm_StochIneqPO_DBar_lemma3_dbar_eq_of_le
-- name    : StochIneqPO.DBar.lemma3_dbar_eq_of_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:18.415929+00:00
-- url     : https://prove2.me/theorems/75b2f5d0-8b93-4fe7-97e5-8baf99634257
-- title:
--   Lemma 3 — d̄ of stochastically ordered stationary laws
-- statement:
--   Let $P,Q$ be stationary laws of real-valued two-sided processes, with integrable time-zero coordinates. If $P\prec Q$ on the coordinatewise ordered path space, then
--
--   $$\bar d(P,Q)=\int\omega^0\,Q(d\omega)-\int\omega^0\,P(d\omega).$$
--
--   The result evaluates the distance exactly for ordered processes and is used in both directions of Theorem 8.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Lemma 3, p. 910 (PDF p. 12)

import Mathlib
import Definitions.Def_StochIneqPO_Comparison_StochLE
import Definitions.Def_StochIneqPO_DBar_IsShiftInvariant
import Definitions.Def_StochIneqPO_DBar_dbar

namespace StochIneqPO.DBar

open MeasureTheory

/-- Lemma 3, p. 910: under stochastic order, `d̄` is the difference of means. -/
theorem lemma3_dbar_eq_of_le
    (P Q : Measure (ℤ → ℝ))
    (hP : IsShiftInvariant P) (hQ : IsShiftInvariant Q)
    (hPi : Integrable (fun ω : ℤ → ℝ => ω 0) P)
    (hQi : Integrable (fun ω : ℤ → ℝ => ω 0) Q)
    (hPQ : StochIneqPO.Comparison.StochLE P Q) :
    dbar P Q = (∫ ω, ω 0 ∂Q) - (∫ ω, ω 0 ∂P) := by sorry

end StochIneqPO.DBar
