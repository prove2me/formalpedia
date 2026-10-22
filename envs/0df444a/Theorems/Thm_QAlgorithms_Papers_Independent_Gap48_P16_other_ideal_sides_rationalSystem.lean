-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P16_other_ideal_sides_rationalSystem
-- name    : QAlgorithms.Papers.Independent.Gap48.P16.other_ideal_sides_rationalSystem
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-21T21:57:04.28417+00:00
-- url     : https://prove2.me/theorems/a508a045-b7d4-4e18-b7ff-f469aa41377a
-- title:
--   Remark 4.4: right and two-sided variants
-- statement:
--   Let $R$ be a commutative noetherian unital ring and let $A$ be an associative unital $R$-algebra. Property $P_r$ means that every cofinite right ideal contains a right ideal with finite projective $R$-module quotient. Property $P$ is the analogous statement for two-sided ideals. Both implications hold:
--
--   $$
--   P_r(A)\ \Longrightarrow\ (A^\circ,A,\operatorname{ev})\text{ is rational},
--   \qquad
--   P(A)\ \Longrightarrow\ (A^\circ,A,\operatorname{ev})\text{ is rational}.
--   $$
--
--   The two conclusions assert injectivity of the evaluation tensor map for every $R$-module. They do not identify the three ideal properties with one another.
-- source:
--   Duality and Rational Modules in Hopf Algebras over Commutative Rings, arXiv:math/0011207v1, PDF p. 13, Remark 4.4: right and two-sided variants

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P16

noncomputable section

universe u

namespace QAlgorithms.Papers.Independent.Gap48.P16

open scoped TensorProduct

section Cofinite

variable (R A : Type u) [CommRing R] [Ring A] [Algebra R A]

variable {R A}

/-- Remark 4.4, PDF p.13: right and two-sided sufficient conditions, separately. -/
theorem other_ideal_sides_rationalSystem [IsNoetherianRing R] :
    (PropertyRight R A → IsRationalSystem (R := R) (A := A) (P := finiteDual R A) (finiteDualPairing R A)) ∧
    (PropertyTwoSided R A → IsRationalSystem (R := R) (A := A) (P := finiteDual R A) (finiteDualPairing R A)) := by sorry

end Cofinite

end QAlgorithms.Papers.Independent.Gap48.P16

end
