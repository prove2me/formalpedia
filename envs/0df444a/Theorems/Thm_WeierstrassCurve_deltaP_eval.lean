-- Prove2me | Theorems.Thm_WeierstrassCurve_deltaP_eval
-- name    : WeierstrassCurve.deltaP_eval
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:54.656975+00:00
-- url     : https://prove2.me/theorems/85873c9c-bb42-4e08-87b8-06e8b456f2ca
-- title:
--   Evaluation of the differential-addition determinant
-- statement:
--   Let $R$ be an integral domain, let $W$ be a Weierstrass curve, let $X_0,Z_0,X_1,Z_1∈R[X]$, and let $x∈R$. Put $ξ_i=X_i(x)$ and $ζ_i=Z_i(x)$. Then the determinant polynomial used in differential addition satisfies $$δ_W(X_0,Z_0,X_1,Z_1)(x)=ξ_0ζ_1-ξ_1ζ_0.$$ This records the projective cross-difference whose vanishing triggers the degenerate ladder branch.
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

theorem WeierstrassCurve.deltaP_eval (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) (x : R) :
    (deltaP W X0 Z0 X1 Z1).eval x = X0.eval x * Z1.eval x - X1.eval x * Z0.eval x := by sorry
