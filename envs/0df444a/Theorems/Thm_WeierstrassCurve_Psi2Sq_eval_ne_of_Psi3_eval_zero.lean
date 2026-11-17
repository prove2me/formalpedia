-- Prove2me | Theorems.Thm_WeierstrassCurve_Psi2Sq_eval_ne_of_Psi3_eval_zero
-- name    : WeierstrassCurve.Psi2Sq_eval_ne_of_Psi3_eval_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:27.9258+00:00
-- url     : https://prove2.me/theorems/72b2780d-e2f3-4db3-98a3-67d460c34a7c
-- title:
--   A root of the third division polynomial is not a root of the squared second
-- statement:
--   Let $k$ be a field, let $W/k$ be an elliptic Weierstrass curve, and let $x∈k$. If the third division polynomial vanishes at $x$, then the squared second division polynomial does not: $$Ψ_3(x)=0 ⇒ Ψ_2^2(x)≠0.$$ This is the converse root-separation statement needed for the exceptional ladder cases.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneResultantCerts
import Definitions.Def_WardSomos

open Polynomial
open scoped Polynomial
open FLT.EDS
open WeierstrassCurve
variable {k : Type*} [Field k]

theorem WeierstrassCurve.Psi2Sq_eval_ne_of_Psi3_eval_zero (W : WeierstrassCurve k) [W.IsElliptic] {x : k}
    (hc3 : W.Ψ₃.eval x = 0) : W.Ψ₂Sq.eval x ≠ 0 := by sorry
