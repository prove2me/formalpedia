-- Prove2me | Theorems.Thm_Rudin_ch06_upper_lower_integral_additive
-- name    : Rudin.ch06_upper_lower_integral_additive
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T14:47:25.821587+00:00
-- url     : https://prove2.me/theorems/429c3914-45ce-4f1f-9132-7c1117d0f132
-- title:
--   Theorem 6.12(c), sharpened — the upper and the lower integral are each additive over adjacent intervals
-- statement:
--   Let $a \le c \le b$, let $\alpha$ be monotonically increasing on $[a,b]$, and let $f$ be bounded on $[a,b]$ (Rudin's standing hypothesis of Definition 6.2, which the formalization must state explicitly because upper and lower integrals are ordinary suprema and infima here). Then, with no integrability assumed,
--
--   $$\overline{\int_a^b} f\,d\alpha = \overline{\int_a^c} f\,d\alpha + \overline{\int_c^b} f\,d\alpha, \qquad \underline{\int_a^b} f\,d\alpha = \underline{\int_a^c} f\,d\alpha + \underline{\int_c^b} f\,d\alpha .$$
--
--   This is the mechanism behind Rudin's Theorem 6.12(c): splitting the interval is a property of the two Darboux extrema separately, and integrability of $f$ on $[a,b]$ — or on the two pieces — is only used afterwards, to identify the upper and lower integrals with one another. In particular the statement yields both directions of 6.12(c): integrability on $[a,b]$ gives integrability on $[a,c]$ and $[c,b]$ with additive integrals, and conversely integrability on the two pieces gives integrability on $[a,b]$.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 128, Theorem 6.12(c) (sharpened form: additivity of the upper and lower integrals separately)

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- For a bounded integrand and a monotonically increasing integrator, the upper integral and the
lower integral are each additive over adjacent intervals; no integrability is assumed. -/
theorem ch06_upper_lower_integral_additive (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M) :
    upperIntegral a b f α = upperIntegral a c f α + upperIntegral c b f α ∧
    lowerIntegral a b f α = lowerIntegral a c f α + lowerIntegral c b f α := by sorry

end Rudin
