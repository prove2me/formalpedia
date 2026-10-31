-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P40_cyclotomicCenter_powerSum_generators
-- name    : QAlgorithms.Papers.Independent.Intake100.P40.cyclotomicCenter_powerSum_generators
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:19:27.358485+00:00
-- url     : https://prove2.me/theorems/2164b323-6469-44ee-856d-1705f4d70a64
-- title:
--   The first d power sums generate the cyclotomic center
-- statement:
--   Let $R$ be a commutative unital ring, $l\ge1$, $d\ge0$, and let $f(X)=X^l+\sum_{a<l}c_aX^a$ be monic. Let $H_d^f$ be the degenerate cyclotomic Hecke algebra with $s_ix_{i+1}=x_is_i+1$ and $f(x_1)=0$, with $H_0^f=R$. If $d!$ is a unit in $R$, then
--
--   $$Z(H_d^f)=R\left[x_1^r+\cdots+x_d^r:1\le r\le d\right].$$
--
--   These are the first $d$ power sums, and generation is as an $R$-algebra. For $d=0$ the empty generating family gives the scalar algebra.
--
--   This is a finite generator description of the center under the factorial-unit hypothesis.
-- source:
--   Centers of degenerate cyclotomic Hecke algebras and parabolic category O, arXiv:math/0607717v3, PDF p. 12, Corollary 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P40

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P40

attribute [local instance] Classical.propDecidable

/-- Corollary 3.3, PDF p.12. These are the first d power sums, including
the empty generating family at d=0. -/
theorem cyclotomicCenter_powerSum_generators (R : Type*) [CommRing R]
    (l d : ℕ) (hl : 0 < l) (c : Fin l → R) (hd : IsUnit (Nat.factorial d : R)) :
    Algebra.adjoin R {z : CyclotomicAlgebra R l d c |
      ∃ r : ℕ, 1 ≤ r ∧ r ≤ d ∧ z = cyclotomicPowerSum R l d c r} =
      Subalgebra.center R (CyclotomicAlgebra R l d c) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P40

end
