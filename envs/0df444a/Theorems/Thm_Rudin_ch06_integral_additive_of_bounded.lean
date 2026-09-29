-- Prove2me | Theorems.Thm_Rudin_ch06_integral_additive_of_bounded
-- name    : Rudin.ch06_integral_additive_of_bounded
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-18T13:03:37.242604+00:00
-- url     : https://prove2.me/theorems/e46ab287-a484-46ee-b9b5-92e66398fd69
-- title:
--   Theorem 6.12(c) — additivity of the integral over adjacent intervals
-- statement:
--   Let $\\alpha$ be monotonically increasing on $[a,b]$ and let $f$ be a bounded real function on $[a,b]$ which is Riemann--Stieltjes integrable with respect to $\\alpha$, written $f \\in \\mathcal{R}(\\alpha)$. This is the additivity of the integral over adjacent intervals: for every $c$ with $a \\le c \\le b$,
--
--   $$f \\in \\mathcal{R}(\\alpha) \\text{ on } [a,c] \\quad\\text{and}\\quad f \\in \\mathcal{R}(\\alpha) \\text{ on } [c,b], \\qquad \\int_a^c f\\,d\\alpha + \\int_c^b f\\,d\\alpha = \\int_a^b f\\,d\\alpha .$$
--
--   Here $\\int_a^b f\\,d\\alpha$ is the common value of the upper integral $\\inf_P U(P,f,\\alpha)$ and the lower integral $\\sup_P L(P,f,\\alpha)$ taken over all partitions $P$ of the interval, as in Rudin's Definition 6.2.
--
--   This is assertion (c) of Rudin's Theorem 6.12, isolated as a reusable lemma: it is the statement that lets an integral be computed piecewise, and it is used throughout the chapter and in the theory of the indefinite integral $F(x) = \\int_a^x f\\,dt$.
--
--   **Formalization Note** Rudin's Definition 6.2 assumes throughout that the integrand is bounded on the interval of integration; that hypothesis is stated explicitly here as `hfb`, since the formalized upper and lower integrals are ordinary suprema and infima of sets of real numbers, which take a default value on unbounded sets. The endpoint cases $c = a$ and $c = b$ are included and are degenerate.
-- source:
--   Walter Rudin, Principles of Mathematical Analysis, 3rd edition, McGraw-Hill, 1976, Chapter 6, pp. 128-129, Theorem 6.12(c) (with the boundedness hypothesis of Definition 6.2)

import Mathlib
import Definitions.Def_Rudin_ch06_stieltjes

open Filter Topology

namespace Rudin

/-- Rudin, Theorem 6.12(c), with the boundedness hypothesis of Chapter 6: if `f` is bounded and
integrable with respect to a monotonically increasing `α` on `[a, b]`, then `f` is integrable on
each of `[a, c]` and `[c, b]` for `c ∈ [a, b]`, and the two integrals add up to the integral over
`[a, b]`. -/
theorem ch06_integral_additive_of_bounded (a b : ℝ) (hab : a ≤ b) (f α : ℝ → ℝ)
    (hα : MonotoneOn α (Set.Icc a b))
    (hfb : ∃ M, ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    (hf : RSIntegrable a b f α) :
    ∀ c ∈ Set.Icc a b, RSIntegrable a c f α ∧ RSIntegrable c b f α ∧
      RSIntegral a c f α + RSIntegral c b f α = RSIntegral a b f α := by sorry

end Rudin
