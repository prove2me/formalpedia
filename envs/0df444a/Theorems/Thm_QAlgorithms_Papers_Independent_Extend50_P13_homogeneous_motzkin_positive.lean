-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_homogeneous_motzkin_positive
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.homogeneous_motzkin_positive
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:49:35.629408+00:00
-- url     : https://prove2.me/theorems/6dd0da88-0f71-49f1-a05b-89afb6a149ef
-- title:
--   Unnumbered homogeneous Motzkin inequality, Eq.(72)
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. For every $A,B\ge0$, define
--
--   $$\widetilde M(A,B)=(\operatorname{tr}A)^2AB^4A+(\operatorname{tr}B)^2A^2B^2A^2-3(\operatorname{tr}A)^2(\operatorname{tr}B)^2AB^2A+(\operatorname{tr}A)^4(\operatorname{tr}B)^4I.$$
--
--   Then $\widetilde M(A,B)\ge0$. There are no trace-one assumptions and no trace denominators; zero inputs are included. This homogenizes the Motzkin matrix inequality on the whole positive cone.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 17, Unnumbered homogeneous Motzkin inequality, Eq.(72)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Homogeneous Motzkin inequality, Eq.72 (PDF p.17). Zero PSD inputs are
included, and the formula has no trace denominators. -/
theorem homogeneous_motzkin_positive {d : ℕ} (hd : 0 < d)
    (A B : (Matrix (Fin d) (Fin d) ℂ)) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (homogeneousMotzkin A B).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
