-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P40_gradedCenter_murphyM_basis
-- name    : QAlgorithms.Papers.Independent.Intake100.P40.gradedCenter_murphyM_basis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:18:51.640654+00:00
-- url     : https://prove2.me/theorems/1dedc709-2516-40dd-9ab2-2c43e5c31acf
-- title:
--   Murphy monomial basis of the graded center
-- statement:
--   Let $R$ be a commutative unital ring, $l\ge1$, $d\ge0$, and $T=R[x_1,\ldots,x_d]/(x_1^l,\ldots,x_d^l)$. For a partition $\mu$, write $|\mu/l|=\sum_j\lfloor\mu_j/l\rfloor$ and set $P_d(l)=\{\mu:\ell(\mu)+|\mu/l|\le d\}$. Pad $\mu$ with zeros to $d$ entries. Define
--
--   $$m_d(\mu)=\sum_{\eta\sim\mu}y_1(\eta_1)\cdots y_d(\eta_d),$$
--
--   summing over distinct rearrangements. If $k=(a-1)l+r$ with $0\le r<l$, then $y_i(k)$ is the sum of $(i_1\cdots i_{a-1}i)^{(r)}$ over ordered distinct letters below $i$. A colored cycle is $A^{(r)}=h_r(A)A$, where $h_r(A)$ is the truncated complete symmetric sum of degree $(|A|-1)(l-1)+r$. Then
--
--   $$\{m_d(\mu):\mu\in P_d(l)\}\text{ is an }R\text{-basis of }Z(T\rtimes RS_d).$$
--
--   This gives the second explicit central basis used to describe the cyclotomic center.
-- source:
--   Centers of degenerate cyclotomic Hecke algebras and parabolic category O, arXiv:math/0607717v3, PDF p. 9, Theorem 2.7

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P40

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P40

attribute [local instance] Classical.propDecidable

/-- Theorem 2.7, PDF pp.9--10. The explicit m_d(mu) basis is indexed by
length(mu)+sum floor(mu_i/l) ≤ d and uses distinct rearrangements. -/
theorem gradedCenter_murphyM_basis (R : Type*) [CommRing R] (l d : ℕ)
    (hl : 0 < l) :
    IsBasisFor (fun mu : PartitionIndex l d => murphyM R l d mu.val)
      (Subalgebra.center R (GradedAlgebra R l d)).toSubmodule := by sorry

end QAlgorithms.Papers.Independent.Intake100.P40

end
