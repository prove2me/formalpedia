-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P27_roots_on_uniq
-- name    : QAlgorithms.Papers.Independent.Dependency50.P27.roots_on_uniq
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T08:49:01.77399+00:00
-- url     : https://prove2.me/theorems/6449488b-06d5-4c48-b9fc-1e1f036df7b0
-- title:
--   §4.2, Lemma roots_on_uniq
-- statement:
--   Let $R$ be a discrete ordered field equipped with a witness-returning intermediate value operation for polynomials. No completeness or Archimedean hypothesis is imposed. Let $s_1,s_2$ be strictly increasing finite lists. Suppose each list has exactly the points $x$ with $a<x<b$ and $P(x)=0$. Then
--
--   $$s_1=s_2.$$
--
--   No nonzero or endpoint-order hypothesis is added. For $P=0$ on a nonempty interval, the finite exhaustive-list hypotheses are impossible.
-- source:
--   Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination, arXiv:1201.3731v2, PDF p. 19, §4.2, Lemma roots_on_uniq

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

namespace QAlgorithms.Papers.Independent.Dependency50.P27

noncomputable section

open Polynomial

/-- Source PDF p. 19, roots_on_uniq; no nonzero or endpoint-order guard. -/
theorem roots_on_uniq {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (a b : R) (s1 s2 : List R)
    (h1 : s1.Pairwise (· < ·)) (h2 : s2.Pairwise (· < ·))
    (hr1 : rootsOn p a b s1) (hr2 : rootsOn p a b s2) : s1 = s2 := by sorry

end

end QAlgorithms.Papers.Independent.Dependency50.P27
