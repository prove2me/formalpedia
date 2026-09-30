-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_quotient_multiplication_drazin_inverse
-- name    : WeierstrassEllipticZeta.quotient_multiplication_drazin_inverse
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T01:40:43.9787+00:00
-- url     : https://prove2.me/theorems/4da03a4a-0d77-4dff-8f00-0bdcbbf0ed3d
-- title:
--   Unique generalized inverse from nilpotent and invertible quotient factors
-- statement:
--   Let $A$ be a commutative ring, and let $I,J,R$ be ideals satisfying
--   $$J+R=A,\qquad J\cap R=I.$$
--   Fix $p\in A$ and a nonnegative integer $d$. Suppose that the image of $p$ in $A/J$ has $d$th power zero and that the image of $p$ in $A/R$ is a unit.
--
--   Writing $a$ for the class of $p$ in $A/I$, there exists a unique $b\in A/I$ such that
--   $$ab^2=b,\qquad a^{d+1}b=a^d.$$
--
--   These are the generalized inverse relations of index at most $d$ in a commutative ring. Under the canonical Chinese remainder isomorphism, the inverse is zero in the nilpotent factor and the ordinary inverse in the unit factor. The theorem requires no field or finite-dimensionality assumption. Exponent $d=0$ is included; its nilpotence hypothesis then forces $A/J$ to be the zero ring. Uniqueness is asserted in the quotient $A/I$.
-- source:
--   Derived commutative-ring lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This lemma is proved here and is not quoted from the article. For comaximal ideals J and R with intersection I, if p is nilpotent to exponent d modulo J and invertible modulo R, there is a unique b modulo I satisfying p*b*b=b and p^(d+1)*b=p^d. It is zero in the nilpotent factor and the ordinary inverse in the unit factor. Primary Mathlib references: Ideal.quotientInfEquivQuotientProd and its projection lemmas, Commute.isNilpotent_mul_right, IsNilpotent.isUnit_one_sub, IsUnit.mul_right_cancel and IsUnit.mul_left_cancel. No Prove2Me theorem dependencies or new definitions.

import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nilpotent.Basic

open scoped Classical

theorem WeierstrassEllipticZeta.quotient_multiplication_drazin_inverse
    (A : Type*) [CommRing A] (I J R : Ideal A) (d : ℕ) (p : A)
    (hsum : J ⊔ R = ⊤) (hinf : J ⊓ R = I)
    (hnil : (Ideal.Quotient.mk J p) ^ d = 0)
    (hunit : IsUnit (Ideal.Quotient.mk R p)) :
    ∃! b : A ⧸ I,
      Ideal.Quotient.mk I p * b * b = b ∧
      (Ideal.Quotient.mk I p) ^ (d + 1) * b = (Ideal.Quotient.mk I p) ^ d := by sorry
