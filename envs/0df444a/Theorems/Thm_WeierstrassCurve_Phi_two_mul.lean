-- Prove2me | Theorems.Thm_WeierstrassCurve_Phi_two_mul
-- name    : WeierstrassCurve.Phi_two_mul
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:03:01.487197+00:00
-- url     : https://prove2.me/theorems/35d7b212-fdcd-44fb-9ad7-67be74285df8
-- title:
--   The even-index x-coordinate numerator obeys the doubling formula
-- statement:
--   Let $R$ be an integral domain, let $W$ be a Weierstrass curve over $R$, assume $4≠0$, assume $ψ_k≠0$ for every nonzero $k∈ℤ$, and assume $Ψ_3≠0$. Write $Φ_n$ for the division-polynomial x-coordinate numerator, $S_n=ΨSq_n$ for the squared denominator, and $N_W$ for the homogeneous doubling numerator. Then for every $m∈ℤ$, $$Φ_{2m}=N_W(Φ_m,S_m).$$ This supplies the numerator half of the EDS doubling certificate.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Definitions.Def_KeystoneDoubling
import Definitions.Def_WardSomos

open Polynomial
open scoped Polynomial
open FLT.EDS
open WeierstrassCurve
variable {R : Type*} [CommRing R] [IsDomain R]

theorem WeierstrassCurve.Phi_two_mul
    (W : WeierstrassCurve R)
    (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0)
    (hc3 : W.Ψ₃ ≠ 0)
    (m : ℤ) :
    W.Φ (2*m) = dupNumP W (W.Φ m) (W.ΨSq m) := by sorry
