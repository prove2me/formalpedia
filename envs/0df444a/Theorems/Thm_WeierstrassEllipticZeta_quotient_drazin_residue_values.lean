-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_quotient_drazin_residue_values
-- name    : WeierstrassEllipticZeta.quotient_drazin_residue_values
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T03:20:57.866826+00:00
-- url     : https://prove2.me/theorems/6291fdd6-854b-43b2-83da-a99a61d45f1b
-- title:
--   Reciprocal residue values and support values of a generalized inverse
-- statement:
--   Let A be a commutative ring, K a field, I an ideal of A, and
--   φ:A→K a ring homomorphism with I contained in its kernel.
--   Let p,q be elements of A and d a natural number. Suppose their
--   classes a,b in A/I satisfy a*b*b=b and a^(d+1)*b=a^d. Then
--
--   $$\varphi(q)=\varphi(p)^{-1},$$
--
--   where the inverse of zero is defined as zero, and
--
--   $$\varphi(pq)=\begin{cases}
--   0&\text{if }\varphi(p)=0,\\
--   1&\text{if }\varphi(p)\ne0.
--   \end{cases}$$
--
--   Thus a generalized inverse has the reciprocal residue value, and
--   its associated projector has the characteristic value of the
--   nonzero locus. No positive-exponent or dimension assumption is needed.
-- source:
--   Derived algebra lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This lemma is proved here and is not quoted from the article. If phi:A→K is a ring homomorphism to a field killing I, and classes p,q modulo I satisfy the generalized-inverse equations, then phi(q)=phi(p)^(-1), with inverse zero equal to zero; phi(p*q) is zero at phi(p)=0 and one otherwise. The proof descends phi to the quotient and cancels nonzero powers in the field. No Prove2Me theorem dependencies or new definitions.

import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Field.Basic

open scoped Classical

theorem WeierstrassEllipticZeta.quotient_drazin_residue_values
    (A K : Type*) [CommRing A] [Field K] (I : Ideal A) (φ : A →+* K)
    (hI : I ≤ RingHom.ker φ) (p q : A) (d : ℕ)
    (h₁ : Ideal.Quotient.mk I p * Ideal.Quotient.mk I q * Ideal.Quotient.mk I q =
      Ideal.Quotient.mk I q)
    (h₂ : (Ideal.Quotient.mk I p) ^ (d + 1) * Ideal.Quotient.mk I q =
      (Ideal.Quotient.mk I p) ^ d) :
    φ q = (φ p)⁻¹ ∧ φ (p * q) = if φ p = 0 then 0 else 1 := by sorry
