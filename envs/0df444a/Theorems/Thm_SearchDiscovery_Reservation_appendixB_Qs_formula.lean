-- Prove2me | Theorems.Thm_SearchDiscovery_Reservation_appendixB_Qs_formula
-- name    : SearchDiscovery.Reservation.appendixB_Qs_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:39.017998+00:00
-- url     : https://prove2.me/theorems/5e58bc05-3204-475b-a9c9-918a2d209e8f
-- title:
--   (7) and Appendix B, pp. 12, 42 — Q_s as an integral of the tail of F over (z − x, ∞)
-- statement:
--   Fix a partial valuation $x$ and let $F$ be the cumulative distribution function of $F_{Y\mid X=x}$. For every outside option $z\in\mathbb R$,
--   $$Q_s(x,c_s,z)=\int_{(z-x,\infty)}(x+y-z)\,\mathrm dF(y)-c_s=\int_{z-x}^{\infty}\big[1-F(y)\big]\,\mathrm dy-c_s .$$
--   The first integral is against the law of $Y$ given $X=x$; the second against Lebesgue measure.
--
--   Substituting $\xi=z-x$, the search value is $z^s=x+\xi$ where $\xi$ solves $\int_\xi^\infty[1-F(y)]\,\mathrm dy=c_s$, which is (7). The tail-integral form is the one used for computation and for the comparative statics of the search value.
--
--   **Formalization Note.** $F$ is `ProbabilityTheory.cdf (κ x)`; both integrals are set integrals over the open half-line $(z-x,\infty)$.
-- source:
--   Greminger, Optimal Search and Discovery, arXiv:1911.07773v5, p. 12, (7); p. 42, Appendix B (display for Q_s)

import Mathlib
import Definitions.Def_SearchDiscovery_Reservation_Model

namespace SearchDiscovery.Reservation

open MeasureTheory ProbabilityTheory

theorem appendixB_Qs_formula (M : SDModel) (hM : M.Standing) (x z : ℝ) :
    M.Qs x z = (∫ y in Set.Ioi (z - x), (x + y - z) ∂M.κ x) - M.cs ∧
    M.Qs x z = (∫ y in Set.Ioi (z - x), (1 - cdf (M.κ x) y)) - M.cs := by sorry

end SearchDiscovery.Reservation
