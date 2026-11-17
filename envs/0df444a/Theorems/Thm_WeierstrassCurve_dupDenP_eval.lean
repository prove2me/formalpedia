-- Prove2me | Theorems.Thm_WeierstrassCurve_dupDenP_eval
-- name    : WeierstrassCurve.dupDenP_eval
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:45.57778+00:00
-- url     : https://prove2.me/theorems/e6838bc4-714d-4e61-9f39-210df626e861
-- title:
--   Evaluation of the homogeneous doubling denominator
-- statement:
--   Let $R$ be a commutative ring, let $W$ be a Weierstrass curve with invariants $b_2,b_4,b_6$, let $X_c,Z_c∈R[X]$, and let $x∈R$. Put $X=X_c(x)$ and $Z=Z_c(x)$. The homogeneous doubling denominator evaluates as $$D_W(X_c,Z_c)(x)=4X^3Z+b_2X^2Z^2+2b_4XZ^3+b_6Z^4.$$ This is the denominator half of the projective x-coordinate doubling law.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneDoubling

open WeierstrassCurve
open Polynomial
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

theorem WeierstrassCurve.dupDenP_eval (W : WeierstrassCurve R) (Xc Zc : R[X]) (x : R) :
    (W.dupDenP Xc Zc).eval x
      = 4 * (Xc.eval x) ^ 3 * (Zc.eval x) + W.b₂ * (Xc.eval x) ^ 2 * (Zc.eval x) ^ 2
        + 2 * W.b₄ * (Xc.eval x) * (Zc.eval x) ^ 3 + W.b₆ * (Zc.eval x) ^ 4 := by sorry
