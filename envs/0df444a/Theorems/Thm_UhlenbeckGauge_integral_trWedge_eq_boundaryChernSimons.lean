-- Prove2me | Theorems.Thm_UhlenbeckGauge_integral_trWedge_eq_boundaryChernSimons
-- name    : UhlenbeckGauge.integral_trWedge_eq_boundaryChernSimons
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:25:24.898491+00:00
-- url     : https://prove2.me/theorems/acc2ac5a-db6d-48cb-86e5-869481e15e8a
-- title:
--   Fact 3.1.3 — $\int_M\operatorname{tr}(F_A\wedge F_A)=\int_{\partial M}CS(A)$ on a box
-- statement:
--   Let $a\le b$ in $\mathbb R^4$ (coordinatewise), $\Omega=[a,b]$ the closed box, and $A$ a smooth $SU(n)$-connection. Then
--   $$\int_\Omega\operatorname{tr}(F_A\wedge F_A)\,d\mathrm{vol}=\int_{\partial\Omega}CS(A),$$
--   where the right-hand side is the integral of the Chern–Simons three-form over the outward-oriented boundary of the box: the sum over $\mu$ of the integral of $K^\mu(A)$ over the face $x_\mu=b_\mu$ minus that over the face $x_\mu=a_\mu$. This is Fact 3.1.3 for the trivial bundle over a box, where the topological term is zero.
-- source:
--   K. Uhlenbeck, *Equations of Gauge Theory*, lecture notes by L. Fredrickson (Emil Grosswald Lectures, Temple University, February 7-9, 2012), Chapter 3, Section 3.1, pp. 29-32, Fact 3.1.3, eq. (3.6) (p. 32)

import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

theorem integral_trWedge_eq_boundaryChernSimons {n : ℕ} (a b : R4) (hab : a ≤ b)
    (A : Connection n) (hA : IsSUConnection A) :
    ∫ x in Set.Icc a b, trWedge (curvature A x) = boundaryChernSimons a b A := by sorry

end UhlenbeckGauge
