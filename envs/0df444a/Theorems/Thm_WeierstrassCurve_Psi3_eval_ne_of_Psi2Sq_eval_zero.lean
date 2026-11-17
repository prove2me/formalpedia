-- Prove2me | Theorems.Thm_WeierstrassCurve_Psi3_eval_ne_of_Psi2Sq_eval_zero
-- name    : WeierstrassCurve.Psi3_eval_ne_of_Psi2Sq_eval_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:26.077091+00:00
-- url     : https://prove2.me/theorems/cb48668e-57b2-4cda-a25d-d53fc713e2aa
-- title:
--   A root of the squared second division polynomial is not a root of the third
-- statement:
--   Let $k$ be a field, let $W/k$ be an elliptic Weierstrass curve, and let $x∈k$. If the squared second division polynomial vanishes at $x$, then the third division polynomial does not: $$Ψ_2^2(x)=0 ⇒ Ψ_3(x)≠0.$$ This Bézout-type separation is a base nonsingularity certificate for the EDS ladder.
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

theorem WeierstrassCurve.Psi3_eval_ne_of_Psi2Sq_eval_zero (W : WeierstrassCurve k) [W.IsElliptic] {x : k}
    (hs : W.Ψ₂Sq.eval x = 0) : W.Ψ₃.eval x ≠ 0 := by sorry
