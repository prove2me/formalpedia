-- Prove2me | Theorems.Thm_SamuelCahnProphet_IID_aStarIID_spec
-- name    : SamuelCahnProphet.IID.aStarIID_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:55.423775+00:00
-- url     : https://prove2.me/theorems/044eb180-81f0-4602-9332-ebf63c7df73e
-- title:
--   Proof of Theorem 2, p. 1215 — with a = a*, W(1) = W(a*) and 0 < a* < 1
-- statement:
--   For reals $b > 0$ and $c > 0$ let
--   $$
--   a^* = \frac{c(1 - e^{-b}) - b e^{-b}(1 - e^{-c})}{c(1 - e^{-b-c})}.
--   $$
--   Then $W(a^*) = W(1)$, that is,
--   $$
--   \frac{(1 - e^{-b-c})(b + a^* c)}{b + c} = 1 - e^{-b},
--   $$
--   and $0 < a^* < 1$.
--
--   Choosing $a = a^*$ makes the two competing threshold rules asymptotically equally good, and $0 < a^* < 1$ makes $a^*$ an admissible middle value of the three-point law.
--
--   **Formalization Note.** $W(a)$ and $W(1)$ are written out as the closed forms of the two preceding milestones, so this is a statement about real numbers only. No hypothesis beyond $b, c > 0$ is assumed.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), p. 1215, proof of Theorem 2, display a* and "then W(1) = W(a*), and 0 < a* < 1"

import Mathlib
import Definitions.Def_SamuelCahnProphet_IID_Setting

open MeasureTheory Filter Topology

namespace SamuelCahnProphet.IID

theorem aStarIID_spec (b c : ℝ) (hb : 0 < b) (hc : 0 < c) :
    (1 - Real.exp (-b - c)) * (b + aStarIID b c * c) / (b + c) = 1 - Real.exp (-b) ∧
      0 < aStarIID b c ∧ aStarIID b c < 1 := by sorry

end SamuelCahnProphet.IID
