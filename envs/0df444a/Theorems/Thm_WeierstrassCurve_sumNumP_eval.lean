-- Prove2me | Theorems.Thm_WeierstrassCurve_sumNumP_eval
-- name    : WeierstrassCurve.sumNumP_eval
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:50.470193+00:00
-- url     : https://prove2.me/theorems/8267cead-4d88-4ef3-a19b-666d9357d7aa
-- title:
--   Evaluation of the Kummer sum numerator
-- statement:
--   Let $R$ be an integral domain, let $W$ be a Weierstrass curve with invariants $b_2,b_4,b_6$, let $X_0,Z_0,X_1,Z_1∈R[X]$, and put $ξ_i=X_i(x)$ and $ζ_i=Z_i(x)$ for $x∈R$. The homogeneous numerator for the sum of the two possible x-coordinates evaluates to $$S_W(x)=2ξ_0ξ_1(ξ_0ζ_1+ξ_1ζ_0)+b_2ξ_0ξ_1ζ_0ζ_1+b_4ζ_0ζ_1(ξ_0ζ_1+ξ_1ζ_0)+b_6ζ_0^2ζ_1^2.$$ This is the symmetric Kummer-line term used in differential addition.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneDiffAddCert
import Definitions.Def_WardSomos

open Polynomial
open scoped Polynomial
open FLT.EDS
open WeierstrassCurve
variable {R : Type*} [CommRing R] [IsDomain R]

theorem WeierstrassCurve.sumNumP_eval (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) (x : R) :
    (sumNumP W X0 Z0 X1 Z1).eval x =
      2 * X0.eval x * X1.eval x * (X0.eval x * Z1.eval x + X1.eval x * Z0.eval x)
        + W.b₂ * X0.eval x * X1.eval x * Z0.eval x * Z1.eval x
        + W.b₄ * Z0.eval x * Z1.eval x * (X0.eval x * Z1.eval x + X1.eval x * Z0.eval x)
        + W.b₆ * (Z0.eval x) ^ 2 * (Z1.eval x) ^ 2 := by sorry
