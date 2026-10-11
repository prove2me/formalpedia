-- Prove2me | Theorems.Thm_UhlenbeckGauge_boundaryChernSimons_eq_of_eq_on_boundary
-- name    : UhlenbeckGauge.boundaryChernSimons_eq_of_eq_on_boundary
-- status  : Proved
-- author  : @SamenHossain
-- created : 2026-10-10T21:38:58.273975+00:00
-- url     : https://prove2.me/theorems/0c4c69cd-fb3d-4442-963c-5dc48c15811e
-- title:
--   Proof of Proposition 3.1.1, p. 31 — the boundary term $\int_{\partial\Omega}CS(A)$ depends only on the boundary data of $A$
-- statement:
--   Let $a\le b$ in $\mathbb R^4$ (coordinatewise) and let $\Omega=[a,b]$ be the closed box. Let $A$ and $B$ be smooth $SU(n)$-connections on the trivial bundle over $\mathbb R^4$ that agree on the boundary of the box: $A_\mu(x)=B_\mu(x)$ for $\mu=0,1,2,3$ at every $x\in\partial\Omega$. Then their Chern–Simons boundary terms coincide,
--   $$\int_{\partial\Omega}CS(A)=\int_{\partial\Omega}CS(B).$$
--   Here $CS(A)=\operatorname{tr}(A\wedge dA+\tfrac23A\wedge A\wedge A)$, and $\int_{\partial\Omega}CS(A)$ is the integral over the outward-oriented boundary: the sum over $\mu$ of the integral of the flux component $K^\mu(A)=\sum_{\nu,\rho,\sigma}\varepsilon_{\mu\nu\rho\sigma}\operatorname{tr}(A_\nu\partial_\rho A_\sigma+\tfrac23A_\nu A_\rho A_\sigma)$ over the face $x_\mu=b_\mu$ minus its integral over the face $x_\mu=a_\mu$.
--
--   This makes precise the remark in the proof of Proposition 3.1.1 that the lower bound for the Yang–Mills energy is "a term depending only on the topology of the $G$-bundle $P$ and the boundary data of the connection". It is the step that lets the energy bound for one connection be compared with the energy of another connection having the same boundary values.
--
--   **Formalization Note** The hypothesis $a\le b$ is needed: if $a_\mu>b_\mu$ for some $\mu$, the box and its boundary are empty while the two face integrals in direction $\mu$ need not vanish. Agreement on the boundary is the platform predicate `OnBoxBoundary`; no condition on derivatives at the boundary is assumed.
-- source:
--   K. Uhlenbeck, Equations of Gauge Theory, lecture notes by L. Fredrickson (Emil Grosswald Lectures, Temple University, 2012), Chapter 3, Section 3.1, proof of Proposition 3.1.1, p. 31 ("the functional is bounded below by a term depending only on the topology of the G-bundle P and the boundary data of the connection"), with the boundary term of Fact 3.1.3, Eq. (3.6), p. 32

import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

/-- The Chern–Simons boundary term depends only on the boundary data of the connection
(Uhlenbeck, *Equations of Gauge Theory*, notes by Fredrickson, §3.1, proof of Proposition 3.1.1,
p. 31: the lower bound for the Yang–Mills functional is "a term depending only on the topology
of the `G`-bundle `P` and the boundary data of the connection"). If `a ≤ b` and two smooth
`SU(n)`-connections agree at every point of the boundary of the box `[a, b]`, then their
Chern–Simons boundary integrals `∫_{∂[a,b]} CS` coincide. -/
theorem boundaryChernSimons_eq_of_eq_on_boundary {n : ℕ} (a b : R4) (hab : a ≤ b)
    (A B : Connection n) (hA : IsSUConnection A) (hB : IsSUConnection B)
    (hbdry : ∀ x, OnBoxBoundary a b x → A x = B x) :
    boundaryChernSimons a b A = boundaryChernSimons a b B := by sorry

end UhlenbeckGauge
