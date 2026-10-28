-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_mvt
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.mvt
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:46:23.66007+00:00
-- url     : https://prove2.me/theorems/c3e94c9a-f8f2-4f58-8e79-33634e3eda94
-- title:
--   §4.1, Lemma mvt
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. For $P\in R[X]$ and $a<b$, there is a point $c$ such that
--
--   $$a<c<b,\qquad P(b)-P(a)=P'(c)(b-a).$$
--
--   The multiplicative identity is the source's mean value theorem for formal polynomial derivatives.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 17, §4.1, Lemma mvt

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 17, mvt, in its multiplicative form. -/
theorem mvt {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (a b : R) (p : Polynomial R) (hab : a < b) :
    ∃ c : R, a < c ∧ c < b ∧
      p.eval b - p.eval a = p.derivative.eval c * (b - a) := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
