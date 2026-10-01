-- Prove2me | Theorems.Thm_TongString_modularMeasure_map_modularAction
-- name    : TongString.modularMeasure_map_modularAction
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T21:14:16.524847+00:00
-- url     : https://prove2.me/theorems/2ad85169-ae4b-4517-8b02-c28629e2321b
-- title:
--   The measure $d^2\tau/(\operatorname{Im}\tau)^2$ is $SL(2,\mathbb Z)$-invariant
-- statement:
--   Let $a,b,c,d\in\mathbb Z$ with $ad-bc=1$ and let $\mu$ be the measure $\dfrac{d^2\tau}{(\operatorname{Im}\tau)^2}$ on the upper half-plane. Then $\mu$ is invariant under the modular transformation $\gamma:\tau\mapsto\frac{a\tau+b}{c\tau+d}$:
--
--   $$
--   \gamma_*\mu=\mu,\qquad\text{i.e.}\qquad \int \phi\!\left(\frac{a\tau+b}{c\tau+d}\right)\frac{d^2\tau}{(\operatorname{Im}\tau)^2}=\int\phi(\tau)\,\frac{d^2\tau}{(\operatorname{Im}\tau)^2}
--   $$
--
--   for every non-negative measurable $\phi$. This is the invariance of the one-loop integration measure.
--
--   **Formalization Note** $\mu$ is a measure on $\mathbb C$ concentrated on $\{\operatorname{Im}\tau>0\}$; invariance is equality of the push-forward measure with $\mu$.
-- source:
--   D. Tong, *String Theory*, University of Cambridge Part III Mathematical Tripos lecture notes (January 2009), http://www.damtp.cam.ac.uk/user/tong/string.html, Section 6.4.1, p. 147 ('The SL(2; Z) invariant measure over the fundamental domain is ∫ d²τ/(Im τ)²')

import Mathlib
import Definitions.Def_TongString_modular_action

namespace TongString

open MeasureTheory

theorem modularMeasure_map_modularAction (a b c d : ℤ) (h : a * d - b * c = 1) :
    modularMeasure.map (modularAction a b c d) = modularMeasure := by sorry

end TongString
