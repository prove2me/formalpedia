-- Prove2me | Theorems.Thm_TeamDiversity_WageGap_equation_2
-- name    : TeamDiversity.WageGap.equation_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:20:15.271015+00:00
-- url     : https://prove2.me/theorems/84e48676-3a0f-460a-9512-ed262319d0b3
-- title:
--   Equation (2), p. 18 — V_d > V_s ⇔ ΔS < 2(E[w_s**] − E[w_d*]), Δ = f_s(2) − f_d(2)
-- statement:
--   For any technologies $f_s$, $f_d$, any success value $S$ and any wages $w_s$, $w_d$, with $V_s = 2f_s(2)S - 4E[w_s]$, $V_d = 2f_d(2)S - 4E[w_d]$, $E[w_k] = f_k(2)w_k$ and $\Delta = f_s(2)-f_d(2)$,
--
--   $$V_d > V_s \iff \Delta S < 2\big(E[w_s] - E[w_d]\big).$$
--
--   This is the comparison of the principal's payoffs that defines the threshold $S^*(\delta)$.
-- source:
--   Glover & Kim, Optimal Team Composition: Diversity to Foster Implicit Team Incentives, SSRN working paper 3344922 (June 2020 version), p. 18 (PDF 19), equation (2)

import Mathlib
import Definitions.Def_TeamDiversity_WageGap_Model

namespace TeamDiversity.WageGap

/-- Equation (2), p. 18: `V_d > V_s ⇔ ΔS < 2(E[w_s] − E[w_d])`, for any success value `S` and any
wages `w_s`, `w_d`. -/
theorem equation_2 (fs fd : Tech) (S ws wd : ℝ) :
    Vd fd S wd > Vs fs S ws ↔ Delta fs fd * S < 2 * (expWage fs ws - expWage fd wd) := by sorry

end TeamDiversity.WageGap
