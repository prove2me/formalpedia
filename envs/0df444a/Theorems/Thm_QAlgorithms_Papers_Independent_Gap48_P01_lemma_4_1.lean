-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P01_lemma_4_1
-- name    : QAlgorithms.Papers.Independent.Gap48.P01.lemma_4_1
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T20:47:09.013782+00:00
-- url     : https://prove2.me/theorems/b80e2fb9-62b3-4631-9246-3fbe72c8e48c
-- title:
--   Lemma 4.1
-- statement:
--   Let $S$ be a commutative unital ring and let $a,b\in S$. Assume multiplication by $a$ has zero kernel in $S$, and multiplication by the class of $b$ has zero kernel in $S/aS$. Then
--   $$
--   \forall \bar x\in S/bS,\qquad \bar a\bar x=0\ \Longrightarrow\ \bar x=0.
--   $$
--   Thus the class of $a$ is not a zero divisor in $S/bS$. No integral-domain hypothesis or invertibility conclusion is imposed. This transfers regularity between the two principal quotients.
-- source:
--   On the freeness of the cyclotomic BMW algebras: admissibility and an isomorphism with the cyclotomic Kauffman tangle algebras, arXiv:0911.5284v1, PDF p. 24, Lemma 4.1

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P01

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Gap48.P01

/-- Lemma 4.1, PDF p.24. Regular means multiplication has zero kernel;
no domain assumption and no assertion that the images are units is made. -/
theorem lemma_4_1 (S : Type*) [CommRing S] (a b : S)
    (ha : ∀ x : S, a*x = 0 → x = 0)
    (hb : ∀ x : S ⧸ Ideal.span ({a} : Set S),
      (Ideal.Quotient.mk (Ideal.span ({a} : Set S)) b) * x = 0 → x = 0) :
    ∀ x : S ⧸ Ideal.span ({b} : Set S),
      (Ideal.Quotient.mk (Ideal.span ({b} : Set S)) a) * x = 0 → x = 0 := by sorry

end QAlgorithms.Papers.Independent.Gap48.P01

end
