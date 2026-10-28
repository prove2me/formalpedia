-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_rolle_weak
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.rolle_weak
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T08:45:57.142601+00:00
-- url     : https://prove2.me/theorems/3580b254-0bce-4809-b653-5716ca9e9f98
-- title:
--   §4.1, Lemma rolle_weak
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. For $P\in R[X]$ and $a<b$ satisfying $P(a)=P(b)=0$, there is a point $c$ such that
--
--   $$a<c<b,\qquad P'(c)=0\ \lor\ P(c)=0.$$
--
--   The disjunction is retained: the witness need not be a consecutive or noncritical root.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 17, §4.1, Lemma rolle_weak

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 17, rolle_weak, retaining the disjunction. -/
theorem rolle_weak {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (a b : R) (p : Polynomial R)
    (hab : a < b) (ha : p.eval a = 0) (hb : p.eval b = 0) :
    ∃ c : R, a < c ∧ c < b ∧ (p.derivative.eval c = 0 ∨ p.eval c = 0) := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
