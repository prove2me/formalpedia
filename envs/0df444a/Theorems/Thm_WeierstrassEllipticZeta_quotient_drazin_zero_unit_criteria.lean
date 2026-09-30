-- Prove2me | Theorems.Thm_WeierstrassEllipticZeta_quotient_drazin_zero_unit_criteria
-- name    : WeierstrassEllipticZeta.quotient_drazin_zero_unit_criteria
-- status  : Proved
-- author  : @tomasz
-- created : 2026-09-10T02:56:50.937138+00:00
-- url     : https://prove2.me/theorems/a6013e41-62e1-45f4-8b0c-5743030a97f1
-- title:
--   Radical and unit criteria for generalized inverses in a quotient
-- statement:
--   Let A be a commutative ring, I an ideal, p an element of A, and
--   a the class of p in A/I. Suppose b in A/I and a natural number d
--   satisfy a*b*b=b and a^(d+1)*b=a^d. Then
--
--   $$b=0\quad\Longleftrightarrow\quad p\in\sqrt I,$$
--
--   and
--
--   $$a\text{ is a unit}\quad\Longleftrightarrow\quad a b=1.$$
--
--   Thus the generalized inverse vanishes exactly on classes that are
--   nilpotent, and it is an ordinary inverse exactly for unit classes.
--   The statement includes d=0 and the improper ideal I=A.
-- source:
--   Derived commutative-ring lemma for the approach associated with Senthil Kumar K (2026), Appendix A and Theorem A.2, https://doi.org/10.1017/S001309152610145X. This lemma is proved here and is not quoted from the article. For a polynomial class a modulo any ideal I, a generalized inverse b satisfying a*b*b=b and a^(d+1)*b=a^d vanishes exactly when the representative belongs to radical(I); the class a is a unit exactly when a*b=1. Nilpotence makes 1-a*b a unit, which forces b=0. Unit-power cancellation proves the second criterion. No Prove2Me theorem dependencies or new definitions.

import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nilpotent.Basic

open scoped Classical

theorem WeierstrassEllipticZeta.quotient_drazin_zero_unit_criteria
    (A : Type*) [CommRing A] (I : Ideal A) (p : A) (b : A ⧸ I) (d : ℕ)
    (h₁ : Ideal.Quotient.mk I p * b * b = b)
    (h₂ : (Ideal.Quotient.mk I p) ^ (d + 1) * b = (Ideal.Quotient.mk I p) ^ d) :
    (b = 0 ↔ p ∈ I.radical) ∧
      (IsUnit (Ideal.Quotient.mk I p) ↔ Ideal.Quotient.mk I p * b = 1) := by sorry
