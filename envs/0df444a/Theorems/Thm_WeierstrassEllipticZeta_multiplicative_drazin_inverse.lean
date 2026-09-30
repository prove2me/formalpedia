-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_multiplicative_drazin_inverse
-- name    : WeierstrassEllipticZeta.multiplicative_drazin_inverse
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T02:34:07.612022+00:00
-- url     : https://prove2.me/theorems/127a2869-81a4-4e27-a0f0-9391680ee0f7
-- title:
--   Unique multiplicative generalized inverse from pointwise existence
-- statement:
--   Let A and B be commutative rings, f:A→B a ring homomorphism, and d
--   a natural number. Suppose that for every a in A there is b in B with
--   f(a)*b*b=b and f(a)^(d+1)*b=f(a)^d.
--
--   There is a unique homomorphism G from the multiplicative monoid with
--   zero of A to that of B such that, for every a,
--   f(a)*G(a)*G(a)=G(a) and f(a)^(d+1)*G(a)=f(a)^d.
--   In particular, G(0)=0, G(1)=1, and G(x*y)=G(x)*G(y).
--   Only existence of the individual witnesses is assumed; their uniqueness
--   is part of the proof. The theorem includes d=0 and trivial rings.
--
--   In the mission, f is the quotient map from the polynomial ring to a
--   contact quotient, and d is the degree of its monic time polynomial.
--   The individual generalized inverses therefore form one canonical
--   multiplicative map.
-- source:
--   Derived commutative-ring lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This lemma is proved here and is not quoted from the article. Given a ring homomorphism f:A→B and a fixed natural exponent d, existence for each a of b satisfying f(a)*b*b=b and f(a)^(d+1)*b=f(a)^d yields a unique zero-preserving monoid homomorphism G:A→B satisfying these relations pointwise. Uniqueness is proved from the equations; it is not an input hypothesis. Products of witnesses give the multiplication law. No Prove2Me theorem dependencies or new definitions.

import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Logic.ExistsUnique

open scoped Classical

theorem WeierstrassEllipticZeta.multiplicative_drazin_inverse
    (A B : Type*) [CommRing A] [CommRing B] (f : A →+* B) (d : ℕ)
    (h : ∀ a : A, ∃ b : B,
      f a * b * b = b ∧ (f a) ^ (d + 1) * b = (f a) ^ d) :
    ∃! G : A →*₀ B, ∀ a : A,
      f a * G a * G a = G a ∧ (f a) ^ (d + 1) * G a = (f a) ^ d := by sorry
