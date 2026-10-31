-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P40_polynomialCentralizer_basis
-- name    : QAlgorithms.Papers.Independent.Intake100.P40.polynomialCentralizer_basis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:16:07.597649+00:00
-- url     : https://prove2.me/theorems/b0378200-8d42-4b58-8891-8d6dd306054d
-- title:
--   Explicit colored-product basis of the polynomial centralizer
-- statement:
--   Let $R$ be a commutative unital ring, $l\ge1$, $d\ge0$, $T=R[x_1,\ldots,x_d]/(x_1^l,\ldots,x_d^l)$ and $Q_d$ the centralizer of $T$ in $T\rtimes RS_d$. A colored cycle is $A^{(r)}=h_r(A)A$ with $0\le r<l$, where $h_r(A)$ is the truncated complete symmetric sum of degree $(|A|-1)(l-1)+r$ on its letters. Products over disjoint cycles form an $R$-basis of $Q_d$.
--
--   Index the family canonically by disjoint colored cycles covering every letter, retaining the uniquely determined color-zero singleton at each otherwise unused fixed point. The cardinality of this specified basis is
--
--   $$\sum_{(1^{m_1}2^{m_2}\cdots)\vdash d}\frac{d!}{m_1!m_2!\cdots}\prod_{a\ge1}\left(\frac{l}{a}\right)^{m_a}.$$
--
--   The displayed expression is computed in $\mathbb Q$. This is a statement about a named basis and its index cardinality, so it also applies to the zero ring. For $d=0$ there is one empty product.
--
--   The basis makes the permutation action on the centralizer explicit.
-- source:
--   Centers of degenerate cyclotomic Hecke algebras and parabolic category O, arXiv:math/0607717v3, PDF p. 6, Theorem 2.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P40

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P40

attribute [local instance] Classical.propDecidable

/-- Theorem 2.3, PDF pp.6--7. The rank clause is the exact cardinality of the
specified basis index, so also makes sense over the zero ring. -/
theorem polynomialCentralizer_basis (R : Type*) [CommRing R] (l d : ℕ)
    (hl : 0 < l) :
    IsBasisFor (disjointColoredProductElement R l d) (polynomialCentralizer R l d).toSubmodule ∧
      (Nat.card (ColoredProduct l d) : ℚ) = centralizerIndexCount l d := by sorry

end QAlgorithms.Papers.Independent.Intake100.P40

end
