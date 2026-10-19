-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_rolle
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.rolle
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:45:18.619986+00:00
-- url     : https://prove2.me/theorems/8fd76925-5b1d-42a5-92f7-4fbb7fed2e64
-- title:
--   §4.1, Lemma rolle
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. For $P\in R[X]$ and $a<b$ with $P(a)=P(b)$, there is a point $c$ such that
--
--   $$a<c<b,\qquad P'(c)=0.$$
--
--   Here $P'$ is the formal derivative. Constant and zero polynomials are allowed, and no root enumeration is assumed as input.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 16, §4.1, Lemma rolle

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF pp. 16–17, Rolle's theorem. No nonconstancy or precomputed roots. -/
theorem rolle {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (a b : R) (p : Polynomial R)
    (hab : a < b) (heq : p.eval a = p.eval b) :
    ∃ c : R, a < c ∧ c < b ∧ p.derivative.eval c = 0 := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
