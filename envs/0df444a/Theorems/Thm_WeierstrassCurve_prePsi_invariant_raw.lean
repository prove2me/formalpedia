-- Prove2me | Theorems.Thm_WeierstrassCurve_prePsi_invariant_raw
-- name    : WeierstrassCurve.prePsi_invariant_raw
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:03:05.489518+00:00
-- url     : https://prove2.me/theorems/f7364eb7-d53f-44da-8624-9f98e4ec4088
-- title:
--   The normalized division-polynomial Ward invariant
-- statement:
--   Let $R$ be an integral domain, let $W$ be a Weierstrass curve over $R$, assume $4≠0$, and assume the full division polynomial $ψ_k$ is nonzero for every nonzero $k∈ℤ$. Put $a_n=preΨ_n$, $s=Ψ_2^2$, $q=Ψ_3$, and $r=preΨ_4$, and define $ε_m=s^2$ when $m$ is even and $ε_m=1$ when $m$ is odd. Then for every $m∈ℤ$, $$q(a_{m+2}a_{m-1}^2+a_{m+1}^2a_{m-2}+ε_ma_m^3)=(r+s^2)a_{m+1}a_ma_{m-1}.$$ This is the raw conserved identity from which the projective doubling and differential-addition formulas are obtained.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Mathlib.Tactic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Definitions.Def_PsiInvariant
import Definitions.Def_WardSomos

open Polynomial
open scoped Polynomial
open FLT.EDS
open WeierstrassCurve
variable {R : Type*} [CommRing R]

theorem WeierstrassCurve.prePsi_invariant_raw [IsDomain R] (W : WeierstrassCurve R) (h4 : (4 : R) ≠ 0)
    (hψ_ne : ∀ k : ℤ, k ≠ 0 → W.ψ k ≠ 0) (m : ℤ) :
    W.Ψ₃ * (W.preΨ (m + 2) * W.preΨ (m - 1) ^ 2 + W.preΨ (m + 1) ^ 2 * W.preΨ (m - 2)
            + (if Even m then W.Ψ₂Sq ^ 2 else 1) * W.preΨ m ^ 3)
      = (W.preΨ₄ + W.Ψ₂Sq ^ 2) * (W.preΨ (m + 1) * W.preΨ m * W.preΨ (m - 1)) := by sorry
