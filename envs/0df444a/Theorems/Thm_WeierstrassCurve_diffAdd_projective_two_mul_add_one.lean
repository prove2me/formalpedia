-- Prove2me | Theorems.Thm_WeierstrassCurve_diffAdd_projective_two_mul_add_one
-- name    : WeierstrassCurve.diffAdd_projective_two_mul_add_one
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:02:54.624049+00:00
-- url     : https://prove2.me/theorems/27650109-c4f6-485b-b3e3-06664fc64b38
-- title:
--   The odd-index pair satisfies the projective differential-addition identity
-- statement:
--   Let $R$ be an integral domain, let $W$ be a Weierstrass curve over $R$, assume $4≠0$, assume $ψ_k≠0$ for every nonzero $k∈ℤ$, and assume $Ψ_3≠0$. Let $S_n=ΨSq_n$, and let $N_W^{+}$ and $D_W^{+}$ be the differential-addition numerator and denominator applied to the adjacent pairs $(Φ_m,S_m)$ and $(Φ_{m+1},S_{m+1})$. Then $$Φ_{2m+1}D_W^{+}=S_{2m+1}N_W^{+}.$$ This cross-multiplication identity identifies the odd-index division-polynomial pair projectively with differential addition.
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

theorem WeierstrassCurve.diffAdd_projective_two_mul_add_one (W : WeierstrassCurve R) (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0) (hc3 : W.Ψ₃ ≠ 0) (m : ℤ) :
    W.Φ (2 * m + 1) * diffAddDenP W (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1))
      = W.ΨSq (2 * m + 1) * diffAddNumP W (W.Φ m) (W.ΨSq m) (W.Φ (m + 1)) (W.ΨSq (m + 1)) := by sorry
