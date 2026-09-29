-- Prove2me | Theorems.Thm_Rudin_ch06_integral_glue_of_bounded
-- name    : Rudin.ch06_integral_glue_of_bounded
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T14:47:29.200988+00:00
-- url     : https://prove2.me/theorems/f6bc673f-9e2b-4bcd-b551-6eb34d020bd1
-- title:
--   Theorem 6.12(c), converse direction — integrability on two adjacent intervals glues
-- statement:
--   Let $a \le c \le b$, let $\alpha$ be monotonically increasing on $[a,b]$, and let $f$ be bounded on $[a,b]$. If $f \in \mathcal R(\alpha)$ on $[a,c]$ and $f \in \mathcal R(\alpha)$ on $[c,b]$, then $f \in \mathcal R(\alpha)$ on $[a,b]$ and
--
--   $$\int_a^c f\,d\alpha + \int_c^b f\,d\alpha = \int_a^b f\,d\alpha .$$
--
--   Rudin's Theorem 6.12(c) asserts the implication in the other direction, from integrability on $[a,b]$ to integrability on the two pieces. The converse recorded here is what one uses to integrate a function assembled from pieces — for instance a function with finitely many jumps, integrated by treating each piece separately — and it follows from the same partition constructions, because the upper integral and the lower integral are each additive over adjacent intervals.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, p. 128, Theorem 6.12(c) (converse direction)

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Converse of Rudin, Theorem 6.12(c): a bounded `f` that is integrable on `[a, c]` and on
`[c, b]` is integrable on `[a, b]`, and the two integrals add up to the integral over `[a, b]`. -/
theorem ch06_integral_glue_of_bounded (a c b : ℝ) (hac : a ≤ c) (hcb : c ≤ b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    (h₁ : RSIntegrable a c f α) (h₂ : RSIntegrable c b f α) :
    RSIntegrable a b f α ∧
      RSIntegral a c f α + RSIntegral c b f α = RSIntegral a b f α := by sorry

end Rudin
