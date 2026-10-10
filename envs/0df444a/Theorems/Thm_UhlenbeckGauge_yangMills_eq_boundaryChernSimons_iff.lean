-- Prove2me | Theorems.Thm_UhlenbeckGauge_yangMills_eq_boundaryChernSimons_iff
-- name    : UhlenbeckGauge.yangMills_eq_boundaryChernSimons_iff
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T22:00:42.281619+00:00
-- url     : https://prove2.me/theorems/78540bfb-eca6-4582-82cc-13f773e73b20
-- title:
--   Proposition 3.1.1 (equality case) — equality iff $F_A$ is self-dual or anti-self-dual
-- statement:
--   Let $a,b\in\mathbb R^4$ with $a_\mu<b_\mu$ for every $\mu$, $\Omega=[a,b]$, and let $A$ be a smooth $SU(n)$-connection. Then
--   $$\mathrm{Ym}_\Omega(A)=-\operatorname{Re}\int_{\partial\Omega}CS(A)\iff \star F_A=F_A\text{ on }\Omega,$$
--   $$\mathrm{Ym}_\Omega(A)=\operatorname{Re}\int_{\partial\Omega}CS(A)\iff \star F_A=-F_A\text{ on }\Omega.$$
--   This is the equality statement "with equality if, and only if, $D_A$ is self-dual or anti-self-dual" in the proof of Proposition 3.1.1, for the trivial bundle over a non-degenerate box.
-- source:
--   K. Uhlenbeck, *Equations of Gauge Theory*, lecture notes by L. Fredrickson (Emil Grosswald Lectures, Temple University, February 7-9, 2012), Chapter 3, Section 3.1, pp. 29-32, proof of Proposition 3.1.1, equality case (p. 31)

import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

theorem yangMills_eq_boundaryChernSimons_iff {n : ℕ} (a b : R4) (hab : ∀ μ, a μ < b μ)
    (A : Connection n) (hA : IsSUConnection A) :
    (yangMills a b A = -(boundaryChernSimons a b A).re ↔
        ∀ x ∈ Set.Icc a b, IsSelfDual (curvature A x)) ∧
      (yangMills a b A = (boundaryChernSimons a b A).re ↔
        ∀ x ∈ Set.Icc a b, IsAntiSelfDual (curvature A x)) := by sorry

end UhlenbeckGauge
