-- Prove2me | Theorems.Thm_StochIneqPO_DBar_lemma2_dbar_ge
-- name    : StochIneqPO.DBar.lemma2_dbar_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:36:29.32377+00:00
-- url     : https://prove2.me/theorems/8f489bc1-b7d6-4948-98a1-59838a2c3d1e
-- title:
--   Lemma 2 — d̄ bounds the difference of means
-- statement:
--   Let $P,Q$ be stationary laws of real-valued two-sided processes, with integrable time-zero coordinates. Their Ornstein distance bounds the absolute difference of their time-zero means:
--
--   $$\bar d(P,Q)\geq\left|\int\omega^0\,P(d\omega)-\int\omega^0\,Q(d\omega)\right|.$$
--
--   This is the lower bound used immediately in Lemma 3. The scanned page shows $\geq$; the derived OCR text misreads that sign.
-- source:
--   Kamae, Krengel, O'Brien, Stochastic Inequalities on Partially Ordered Spaces, Ann. Probab. 5 (1977), Lemma 2, p. 910 (PDF p. 12)

import Mathlib
import Definitions.Def_StochIneqPO_DBar_IsShiftInvariant
import Definitions.Def_StochIneqPO_DBar_dbar

namespace StochIneqPO.DBar

open MeasureTheory

/-- Lemma 2, p. 910: `d̄` bounds the difference of the time-zero means. -/
theorem lemma2_dbar_ge
    (P Q : Measure (ℤ → ℝ))
    (hP : IsShiftInvariant P) (hQ : IsShiftInvariant Q)
    (hPi : Integrable (fun ω : ℤ → ℝ => ω 0) P)
    (hQi : Integrable (fun ω : ℤ → ℝ => ω 0) Q) :
    |(∫ ω, ω 0 ∂P) - (∫ ω, ω 0 ∂Q)| ≤ dbar P Q := by sorry

end StochIneqPO.DBar
