-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P40_gradedCenter_singleCycle_generators
-- name    : QAlgorithms.Papers.Independent.Intake100.P40.gradedCenter_singleCycle_generators
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:17:33.36398+00:00
-- url     : https://prove2.me/theorems/74dd2ca1-fc1e-4daa-bd4c-efea5279fdf7
-- title:
--   Single-cycle generators when the factorial is a unit
-- statement:
--   Let $R$ be a commutative unital ring, $l\ge1$, $d\ge0$, $T=R[x_1,\ldots,x_d]/(x_1^l,\ldots,x_d^l)$, and assume $d!$ is a unit in $R$. For $1\le a\le d$ and $0\le r<l$, sum $A^{(r)}=h_r(A)A$ over the distinct marked $a$-cycles $A$ of $S_d$, where $h_r(A)$ is the truncated complete symmetric sum of degree $(a-1)(l-1)+r$. Then
--
--   $$Z(T\rtimes RS_d)=R\left[\sum_{A\text{ an }a\text{-cycle}}A^{(r)}:1\le a\le d,\ 0\le r<l\right].$$
--
--   Generation is as an $R$-algebra. At $d=0$ the family is empty and generates the scalar algebra.
--
--   The result reduces all central orbit sums to single-cycle generators.
-- source:
--   Centers of degenerate cyclotomic Hecke algebras and parabolic category O, arXiv:math/0607717v3, PDF p. 8, Corollary 2.5

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P40

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P40

attribute [local instance] Classical.propDecidable

/-- Corollary 2.5, PDF p.8. Generation is as an R-algebra, with precisely
the source's d!-unit hypothesis and single-cycle sums. -/
theorem gradedCenter_singleCycle_generators (R : Type*) [CommRing R]
    (l d : ℕ) (hl : 0 < l) (hd : IsUnit (Nat.factorial d : R)) :
    Algebra.adjoin R {z : GradedAlgebra R l d |
      ∃ a r : ℕ, 1 ≤ a ∧ a ≤ d ∧ r < l ∧ z = singleCycleSum R l d a r} =
      Subalgebra.center R (GradedAlgebra R l d) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P40

end
