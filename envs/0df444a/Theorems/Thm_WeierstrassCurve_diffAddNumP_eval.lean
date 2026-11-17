-- Prove2me | Theorems.Thm_WeierstrassCurve_diffAddNumP_eval
-- name    : WeierstrassCurve.diffAddNumP_eval
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:47.296276+00:00
-- url     : https://prove2.me/theorems/26ff3dca-4aef-47e8-afa4-dd75fb011072
-- title:
--   Evaluation of the differential-addition numerator
-- statement:
--   Let $R$ be an integral domain, let $W$ be a Weierstrass curve, let $X_0,Z_0,X_1,Z_1∈R[X]$, and let $x∈R$. If $S_W$ is the homogeneous Kummer sum numerator and $δ_W$ is the projective determinant for these two pairs, then the differential-addition numerator satisfies $$N_W^{+}(x)=S_W(x)-δ_W(x)^2x.$$ This is the evaluated numerator formula used to certify the odd ladder step.
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

theorem WeierstrassCurve.diffAddNumP_eval (W : WeierstrassCurve R) (X0 Z0 X1 Z1 : R[X]) (x : R) :
    (diffAddNumP W X0 Z0 X1 Z1).eval x =
      (sumNumP W X0 Z0 X1 Z1).eval x - ((deltaP W X0 Z0 X1 Z1).eval x) ^ 2 * x := by sorry
