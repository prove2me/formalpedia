-- Prove2me | Theorems.Thm_WeierstrassCurve_prePsi4_eval_ne_of_Psi3_eval_zero
-- name    : WeierstrassCurve.prePsi4_eval_ne_of_Psi3_eval_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:03:56.233665+00:00
-- url     : https://prove2.me/theorems/efb1b0bf-710e-4b75-a82c-f744d542c038
-- title:
--   A root of the third division polynomial is not a root of the normalized fourth
-- statement:
--   Let $k$ be a field, let $W/k$ be an elliptic Weierstrass curve, and let $x∈k$. If $Ψ_3(x)=0$, then the normalized fourth division polynomial is nonzero at $x$: $$Ψ_3(x)=0 ⇒ preΨ_4(x)≠0.$$ This prevents adjacent division-polynomial degeneracy in the Keystone coprimality argument.
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

theorem WeierstrassCurve.prePsi4_eval_ne_of_Psi3_eval_zero (W : WeierstrassCurve k) [W.IsElliptic] {x : k}
    (hc3 : W.Ψ₃.eval x = 0) : (W.preΨ 4).eval x ≠ 0 := by sorry
