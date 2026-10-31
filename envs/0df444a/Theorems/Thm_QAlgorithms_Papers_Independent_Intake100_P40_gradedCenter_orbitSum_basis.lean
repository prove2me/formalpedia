-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P40_gradedCenter_orbitSum_basis
-- name    : QAlgorithms.Papers.Independent.Intake100.P40.gradedCenter_orbitSum_basis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:16:45.718577+00:00
-- url     : https://prove2.me/theorems/526f074c-efe3-4358-bb8c-575c68d27db2
-- title:
--   Orbit-sum basis of the graded center
-- statement:
--   Let $R$ be a commutative unital ring, $l\ge1$, $d\ge0$, and $T=R[x_1,\ldots,x_d]/(x_1^l,\ldots,x_d^l)$. For an $l$-multipartition $\lambda$ of $d$, let $z_d(\lambda)$ be the sum of the distinct products of disjoint colored cycles of cycle type $\lambda$ in $T\rtimes RS_d$. Color $r-1$ contributes its cycle lengths to component $\lambda^{(r)}$; all fixed points, including color-zero singletons, contribute to the type. Each colored cycle is $A^{(r)}=h_r(A)A$ with the truncated complete symmetric sum $h_r$ of degree $(|A|-1)(l-1)+r$.
--
--   $$\{z_d(\lambda):\lambda\in M_d(l)\}\text{ is an }R\text{-basis of }Z(T\rtimes RS_d).$$
--
--   In particular the center is free with this specified basis of cardinality $|M_d(l)|$. No assumption on $d!$ is made, and orbit sums have no stabilizer multiplicity.
--
--   This gives a central basis over arbitrary commutative ground rings.
-- source:
--   Centers of degenerate cyclotomic Hecke algebras and parabolic category O, arXiv:math/0607717v3, PDF p. 8, Theorem 2.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P40

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P40

attribute [local instance] Classical.propDecidable

/-- Theorem 2.4, PDF pp.7--8. The named orbit sums form a basis, whose index
is exactly M_d(l); no invertibility of d! is assumed. -/
theorem gradedCenter_orbitSum_basis (R : Type*) [CommRing R] (l d : ℕ)
    (hl : 0 < l) :
    IsBasisFor (orbitSum R l d)
      (Subalgebra.center R (GradedAlgebra R l d)).toSubmodule := by sorry

end QAlgorithms.Papers.Independent.Intake100.P40

end
