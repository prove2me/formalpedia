-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support21_P11_two_strand_spanning
-- name    : QAlgorithms.Papers.Independent.Support21.P11.two_strand_spanning
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T03:58:36.428956+00:00
-- url     : https://prove2.me/theorems/edc20ae0-3cec-4bc7-b0d7-9c9851e21aff
-- title:
--   Explicit spanning families in the two-strand algebra
-- statement:
--   Let $R$ be a commutative ring with identity, let $r\ge1$, let $\omega=(\omega_a)_{a\ge0}$ be an $R$-valued sequence, and let $u_1,\ldots,u_r\in R$. Write $W$ for the two-strand degenerate cyclotomic BMW algebra with these parameters, $e=e_1$, $s=s_1$, and $x=x_1$. Put $\prod_{i=1}^r(z-u_i)=\sum_{j=0}^r a_jz^j$. Write $E=(x^ae)_{0\le a<r}$ and let $B$ be the indexed family of the three monomial types $x_1^ae_1x_1^b$, $x_1^ax_2^bs_1$, and $x_1^ax_2^b$, for $0\le a,b<r$. Then
--
--   $$We=\operatorname{span}_R E,\qquad W=\operatorname{span}_R B.$$
--
--   These spanning assertions hold for arbitrary parameters, before imposing any admissibility, characteristic, or domain restriction. They identify the families that can become bases.
-- source:
--   Admissibility Conditions for Degenerate Cyclotomic BMW Algebras, arXiv:0905.4253v2, PDF p. 4, Lemma 3.1

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P11

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Support21.P11

open QAlgorithms.Papers.Independent.Renew46.P16

/-- Lemma 3.1, PDF p.4: the left ideal equality and spanning of the whole
algebra, over arbitrary commutative ground rings. -/
theorem two_strand_spanning (R : Type*) [CommRing R] (omega : ℕ → R)
    (r : ℕ) (u : Fin r → R) (hr : 1 ≤ r) :
    leftIdeal R omega r u = Submodule.span R (Set.range (idealFamily R omega r u)) ∧
    Submodule.span R (Set.range (algebraFamily R omega r u)) = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Support21.P11

end
