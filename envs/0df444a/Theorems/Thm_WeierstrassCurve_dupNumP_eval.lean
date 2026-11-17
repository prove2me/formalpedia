-- Prove2me | Theorems.Thm_WeierstrassCurve_dupNumP_eval
-- name    : WeierstrassCurve.dupNumP_eval
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:48.731198+00:00
-- url     : https://prove2.me/theorems/3c6cef92-c54e-4d88-a342-bc8ed2acfc1e
-- title:
--   Evaluation of the homogeneous doubling numerator
-- statement:
--   Let $R$ be a commutative ring, let $W$ be a Weierstrass curve with invariants $b_4,b_6,b_8$, let $X_c,Z_c∈R[X]$, and let $x∈R$. Put $X=X_c(x)$ and $Z=Z_c(x)$. The homogeneous doubling numerator evaluates as $$N_W(X_c,Z_c)(x)=X^4-b_4X^2Z^2-2b_6XZ^3-b_8Z^4.$$ This converts the polynomial doubling certificate into the usual homogeneous x-coordinate formula.
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

theorem WeierstrassCurve.dupNumP_eval (W : WeierstrassCurve R) (Xc Zc : R[X]) (x : R) :
    (W.dupNumP Xc Zc).eval x
      = (Xc.eval x) ^ 4 - W.b₄ * (Xc.eval x) ^ 2 * (Zc.eval x) ^ 2
        - 2 * W.b₆ * (Xc.eval x) * (Zc.eval x) ^ 3 - W.b₈ * (Zc.eval x) ^ 4 := by sorry
