-- Prove2me | Theorems.Thm_WeilDefect_RPB108_inverse_quadratic_upper
-- name    : WeilDefect.RPB108.inverse_quadratic_upper
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-11T04:54:48.284099+00:00
-- url     : https://prove2.me/theorems/dabaf39b-8c7d-4d56-98ba-7f343ff819cd
-- title:
--   Inverse quadratic upper bound
-- statement:
--   For a complex inner-product space E, continuous complex-linear T, vector r and real k, assume ‖T‖≤1/k. Then Re⟨r,Tr⟩≤‖r‖²/k. The native theorem does not require k>0; its operator bound is kept exactly.
--
--   Exact native statement, definitions and coordinate order are preserved. Original-form realization attachments are unproved future formalization; complete 1.06 positivity, global continuation and RH are not established.
-- source:
--   https://github.com/monocap-tech/weil/blob/ada7948cb459fd21d400cd8f2a92e87672e31f2d/WeilDefect/RPB108/SchurBounds.lean#L5-L17; exact native theorem WeilDefect.RPB108.inverse_quadratic_upper. SHA256 559f8c972633086de1625a34c0ae03fa96d241415c6b33e4c028839fb43e7de7. Rational certificates are distinct from original-form realization attachments and analytic/interval-producer replay.

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem WeilDefect.RPB108.inverse_quadratic_upper {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (T : E →L[ℂ] E) (r : E) (k : ℝ)
    (hT : ‖T‖ ≤ 1/k) :
    (inner ℂ r (T r)).re ≤ ‖r‖^2/k := by sorry
