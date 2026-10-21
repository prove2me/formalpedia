-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P01_su3_violates_GC4
-- name    : QAlgorithms.Papers.Independent.Renew46.P01.su3_violates_GC4
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T19:42:07.340473+00:00
-- url     : https://prove2.me/theorems/497bb1ef-1d50-478b-aa54-e081180a6951
-- title:
--   The displayed SU(3) octet states violate GC4
-- statement:
--   In the source GT-coupled basis for $3\otimes\overline 3=8\oplus1$, fix the octet and its outer multiplicity label. Write $e_1=|3,1\rangle|\overline3,3\rangle$, $e_2=|3,2\rangle|\overline3,2\rangle$, and $e_3=|3,3\rangle|\overline3,1\rangle$. The two displayed zero-weight octet vectors are
--
--   $$
--   v_0=\frac{e_1+e_2}{\sqrt2},\qquad
--   v_1=-\frac{e_1}{\sqrt6}+\frac{e_2}{\sqrt6}+\sqrt{\frac23}e_3.
--   $$
--
--   They are orthonormal, and their coefficients on the same child product $e_1$ are both nonzero. Therefore the restricted coupling tensor already violates (GC4), which permits at most one nonzero parent state label for each fixed child product.
--
--   This is an explicit existence counterexample for SU(3), without a classical hardness conclusion or a claim about every higher rank.
-- source:
--   Generalised Coupling and An Elementary Algorithm for the Quantum Schur Transform, arXiv:2305.04069v3, PDF p. 18, §IV.D, Eqs.(49)–(51): SU(3) violates GC4

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P01

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P01

open scoped BigOperators ComplexConjugate

attribute [local instance] Classical.propDecidable

/-- PDF p.18, §IV.D, (49)--(51): SU(3) violates GC4, witnessed within
one fixed octet and outer label by the two displayed orthonormal states
with nonzero coefficients on the same child product. No classical
hardness or failure for every N>2 is asserted. -/
theorem su3_violates_GC4 :
    ¬ UniqueParent su3OctetCoefficients ∧
    su3OctetCoefficients 0 (0, 2) ≠ 0 ∧
    su3OctetCoefficients 1 (0, 2) ≠ 0 ∧
    (∀ M N : Fin 2,
      (∑ x : Fin 3 × Fin 3,
        star (su3OctetCoefficients M x) * su3OctetCoefficients N x) =
          if M = N then 1 else 0) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P01

end
