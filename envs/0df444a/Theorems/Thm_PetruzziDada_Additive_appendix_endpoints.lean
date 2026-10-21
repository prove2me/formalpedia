-- Prove2me | Theorems.Thm_PetruzziDada_Additive_appendix_endpoints
-- name    : PetruzziDada.Additive.appendix_endpoints
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:49:15.018145+00:00
-- url     : https://prove2.me/theorems/97bf996b-10e3-4636-b455-73c419e67dc4
-- title:
--   Appendix, proof of Theorem 1 (p. 193) — R(B) = −(c + h) and 2bR(A) = a − b(c − 2s) + A
-- statement:
--   In the additive-demand price-setting newsvendor, let $R(z) = dE[\Pi(z,p(z))]/dz$. At the two ends of the support of the demand noise,
--   $$R(B) = -(c+h) \qquad\text{and}\qquad 2bR(A) = a - b(c-2s) + A.$$
--
--   These are the endpoint values used in the proof of Theorem 1 (p. 193). The second shows that the extra hypothesis $a - b(c-2s) + A > 0$ of Theorem 1(c) is exactly $R(A) > 0$.
--
--   **Formalization Note** The paper writes "$R(B) = -(c+h) < 0$"; only the equality is stated here. The strict inequality needs $c + h > 0$, which the standing assumption $h \ge -c$ does not give (it allows $c + h = 0$).
-- source:
--   Petruzzi & Dada, Pricing and the Newsvendor Problem: A Review with Extensions, Oper. Res. 47(2) 1999, p. 193, Appendix, proof of Theorem 1, R(B) and the value of 2bR(A)

import Mathlib
import Definitions.Def_PetruzziDada_Additive_Model

open MeasureTheory

namespace PetruzziDada.Additive

/-- Appendix, proof of Theorem 1, p. 193: the values of `R = dE[Π(z, p(z))]/dz` at the ends
of `[A, B]`, `R(B) = -(c + h)` and `2bR(A) = a - b(c - 2s) + A`. -/
theorem appendix_endpoints (M : Model) :
    M.R M.B = -(M.c + M.h) ∧ 2 * M.b * M.R M.A = M.a - M.b * (M.c - 2 * M.s) + M.A := by sorry
end PetruzziDada.Additive
