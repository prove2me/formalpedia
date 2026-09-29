-- Prove2me | Theorems.Thm_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic
-- name    : WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:04.363612+00:00
-- url     : https://prove2.me/theorems/25b8df23-3b96-5fb9-9d28-c9426ba8f3fa
-- title:
--   Nonvanishing of Ψ₂² for an elliptic curve in any characteristic
-- statement:
--   Let $F$ be a field and let $W$ be a Weierstrass curve over $F$, given by coefficients $a_1,a_2,a_3,a_4,a_6$, which is assumed to be elliptic in Mathlib's sense, i.e. its discriminant $\Delta$ is a unit of $F$. The assertion is that the polynomial $W.\Psi_2\mathrm{Sq} = 4X^3 + b_2X^2 + 2b_4X + b_6 \in F[X]$, the square of the $2$-division polynomial expressed in the usual invariants $b_2 = a_1^2+4a_2$, $b_4 = 2a_4+a_1a_3$, $b_6 = a_3^2+4a_6$, is not the zero polynomial. No assumption on the characteristic of $F$ is made; in particular this strengthens the form of the statement in which $4 \neq 0$ in $F$ is hypothesised, where the conclusion is immediate from the leading coefficient. The $x$-coordinates of the nontrivial $2$-torsion points of $W$ are exactly the roots of this polynomial, so the conclusion says that the $2$-torsion locus is cut out by a nonzero equation.
--
--   This is the characteristic-free form of the statement that the $2$-division polynomial of an elliptic curve does not vanish identically; in characteristic $2$ it encodes the fact that $a_1$ and $a_3$ cannot both vanish when $\Delta$ is invertible. It is used throughout the treatment of $2$-torsion of elliptic curves, for instance in the work on points of modular curves and on the Čerednik–Drinfel'd uniformisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WeierstrassCurve_Psi2Sq_ne_zero_of_isElliptic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WeierstrassCurve.Psi2Sq_ne_zero_of_isElliptic {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic] : W.Ψ₂Sq ≠ 0 := by sorry
