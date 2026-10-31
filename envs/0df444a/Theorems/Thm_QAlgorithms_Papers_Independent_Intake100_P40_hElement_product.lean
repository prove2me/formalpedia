-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P40_hElement_product
-- name    : QAlgorithms.Papers.Independent.Intake100.P40.hElement_product
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:14:38.366641+00:00
-- url     : https://prove2.me/theorems/2c0e01f9-bcf8-4e3c-9bbb-71f13fc055a8
-- title:
--   Product of truncated complete symmetric functions
-- statement:
--   Let $R$ be a commutative unital ring, $l\ge1$, $d\ge0$, and $T=R[x_1,\ldots,x_d]/(x_1^l,\ldots,x_d^l)$. For a nonempty subset $I$ of $\{1,\ldots,d\}$ define
--
--   $$h_r(I)=\sum_{\substack{0\le e_i<l\ (i\in I)\\ \sum_{i\in I}e_i=(|I|-1)(l-1)+r}}\prod_{i\in I}x_i^{e_i}.$$
--
--   If $I,J\subseteq\{1,\ldots,d\}$ have $c=|I\cap J|>0$ and $r,s\ge0$, then
--
--   $$h_r(I)h_s(J)=l^{c-1}h_{r+s+(c-1)(l-1)}(I\cup J).$$
--
--   The scalar $l$ on the right denotes its image in $R$. The equation is represented in the skew group algebra $T\rtimes RS_d$, which contains $T$ as its polynomial subalgebra.
--
--   This product rule controls intersecting colored cycles.
-- source:
--   Centers of degenerate cyclotomic Hecke algebras and parabolic category O, arXiv:math/0607717v3, PDF p. 4, Lemma 2.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P40

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P40

attribute [local instance] Classical.propDecidable

/-- Lemma 2.1, PDF pp.4--5. The nonempty intersection guards all subtractions
in c-1 and excludes empty letter sets. The scalar l is cast into R. -/
theorem hElement_product (R : Type*) [CommRing R] (l d : ℕ) (hl : 0 < l)
    (I J : Finset (Fin d)) (hIJ : 0 < (I ∩ J).card) (r s : ℕ) :
    hElement R l d I r * hElement R l d J s =
      ((l : R) ^ ((I ∩ J).card - 1)) •
        hElement R l d (I ∪ J) (r + s + ((I ∩ J).card - 1) * (l - 1)) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P40

end
