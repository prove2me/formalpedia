-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P13_motzkin_square_identity_and_positivity
-- name    : QAlgorithms.Papers.Independent.Extend50.P13.motzkin_square_identity_and_positivity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T16:48:55.658593+00:00
-- url     : https://prove2.me/theorems/03de85e1-116d-48d7-88a2-e2754380d3b2
-- title:
--   Unnumbered Motzkin matrix identity and inequality, Eqs.(70)–(71)
-- statement:
--   All matrices are complex, $d\times d$, with $d\ge1$. Write $I$ for the identity and $\operatorname{tr}$ for the ordinary, unnormalized trace. Matrix inequalities use the Löwner order, so $A\ge0$ includes Hermiticity. Let $A,B$ be Hermitian and set $M(A,B)=AB^4A+A^2B^2A^2-3AB^2A+I$. Then
--
--   $$M(A,B)=(A^2-A)B^2(A^2-A)+(AB^2+A^2-2A)(B^2A+A^2-2A)+(I-A)(I+2A-A^2)(I-A).$$
--
--   Consequently,
--
--   $$(1-\sqrt2)I\le A\le(1+\sqrt2)I\quad\Longrightarrow\quad M(A,B)\ge0.$$
--
--   In particular, $A\ge0$ and $\operatorname{tr}A=1$ suffice. No normalization of $B$ is needed beyond its Hermiticity. The identity and positivity argument are the proof communicated by Jurij Volčič and reproduced in the source.
-- source:
--   Positive maps and trace polynomials from the symmetric group, arXiv:2002.12887v2, PDF p. 17, Unnumbered Motzkin matrix identity and inequality, Eqs.(70)–(71)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P13

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P13

attribute [local instance] Classical.propDecidable

/-- Motzkin identity and inequality, Eqs.70–71, including the communicated proof
by Jurij Volcic (PDF p.17). Hermitian B is essential to the square-positivity
reading; no normalization is imposed on B. Matrix bounds are Loewner bounds. -/
theorem motzkin_square_identity_and_positivity {d : ℕ} (hd : 0 < d)
    (A B : (Matrix (Fin d) (Fin d) ℂ)) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    motzkin A B = motzkinSquares A B ∧
    (((A-((1-Real.sqrt 2 : ℝ) : ℂ) • (1 : (Matrix (Fin d) (Fin d) ℂ))).PosSemidef ∧
      ((((1+Real.sqrt 2 : ℝ) : ℂ) • (1 : (Matrix (Fin d) (Fin d) ℂ)))-A).PosSemidef) →
        (motzkin A B).PosSemidef) ∧
    (QAlgorithms.IsDensityMatrix A → (motzkin A B).PosSemidef) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P13

end
