-- Prove2me | Theorems.Thm_UhlenbeckGauge_selfDual_absolute_minimizer
-- name    : UhlenbeckGauge.selfDual_absolute_minimizer
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T22:03:52.67899+00:00
-- url     : https://prove2.me/theorems/540bade1-d585-4bf6-9c68-b022fabf478a
-- title:
--   Proposition 3.1.1 — (anti-)self-dual connections are absolute minimizers of Yang-Mills (box version)
-- statement:
--   Let $a,b\in\mathbb R^4$, $\Omega=[a,b]$ the closed box, and let $A$, $B$ be smooth $SU(n)$-connections on the trivial bundle with the same boundary data, $A=B$ at every point of $\partial\Omega$. Suppose the curvature of $A$ is self-dual at every point of $\Omega$, or anti-self-dual at every point of $\Omega$. Then
--   $$\mathrm{Ym}_\Omega(A)=\int_\Omega|F_A|^2\,d\mathrm{vol}\ \le\ \int_\Omega|F_B|^2\,d\mathrm{vol}=\mathrm{Ym}_\Omega(B).$$
--   That is, solutions of the (anti-)self-dual Yang–Mills equations are absolute minimizers of the Yang–Mills functional among connections with the same boundary values.
--
--   **Formalization Note** The notes state the result within a topological class $c_2(P)=k$ on a general bundle over a four-manifold with boundary; here the bundle is the trivial $SU(n)$-bundle over a closed axis-parallel box in Euclidean $\mathbb R^4$, so there is a single topological class. Connections are smooth on all of $\mathbb R^4$.
-- source:
--   K. Uhlenbeck, *Equations of Gauge Theory*, lecture notes by L. Fredrickson (Emil Grosswald Lectures, Temple University, February 7-9, 2012), Chapter 3, Section 3.1, pp. 29-32, Proposition 3.1.1 (p. 31)

import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

theorem selfDual_absolute_minimizer {n : ℕ} (a b : R4) (A B : Connection n)
    (hA : IsSUConnection A) (hB : IsSUConnection B)
    (hbdry : ∀ x, OnBoxBoundary a b x → A x = B x)
    (hdual : (∀ x ∈ Set.Icc a b, IsSelfDual (curvature A x)) ∨
      (∀ x ∈ Set.Icc a b, IsAntiSelfDual (curvature A x))) :
    yangMills a b A ≤ yangMills a b B := by sorry

end UhlenbeckGauge
