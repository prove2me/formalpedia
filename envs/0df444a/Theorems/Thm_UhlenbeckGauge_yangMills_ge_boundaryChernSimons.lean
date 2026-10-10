-- Prove2me | Theorems.Thm_UhlenbeckGauge_yangMills_ge_boundaryChernSimons
-- name    : UhlenbeckGauge.yangMills_ge_boundaryChernSimons
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:59:54.98028+00:00
-- url     : https://prove2.me/theorems/c5b4e0c6-7e74-4b1a-970a-a4ec86f1793e
-- title:
--   Proposition 3.1.1 (energy bound) — $\mathrm{Ym}(D_A)\ge\mp\int_{\partial M}CS(A)$ on a box
-- statement:
--   Let $a\le b$ in $\mathbb R^4$, $\Omega=[a,b]$, and let $A$ be a smooth $SU(n)$-connection. Then
--   $$\mathrm{Ym}_\Omega(A)\ge-\operatorname{Re}\int_{\partial\Omega}CS(A)\qquad\text{and}\qquad \mathrm{Ym}_\Omega(A)\ge\operatorname{Re}\int_{\partial\Omega}CS(A).$$
--   Thus the Yang–Mills energy is bounded below by a quantity depending only on the boundary values of the connection; this is the inequality $\mathrm{Ym}(D_A)\ge8\pi^2c_2(P)+\int_{\partial M}CS(A)$ of the proof of Proposition 3.1.1, in both sign versions, for the trivial bundle over a box.
-- source:
--   K. Uhlenbeck, *Equations of Gauge Theory*, lecture notes by L. Fredrickson (Emil Grosswald Lectures, Temple University, February 7-9, 2012), Chapter 3, Section 3.1, pp. 29-32, proof of Proposition 3.1.1 (p. 31)

import Definitions.Def_uhlenbeck_gauge_box_defs

open UhlenbeckGauge

namespace UhlenbeckGauge

theorem yangMills_ge_boundaryChernSimons {n : ℕ} (a b : R4) (hab : a ≤ b)
    (A : Connection n) (hA : IsSUConnection A) :
    -(boundaryChernSimons a b A).re ≤ yangMills a b A ∧
      (boundaryChernSimons a b A).re ≤ yangMills a b A := by sorry

end UhlenbeckGauge
