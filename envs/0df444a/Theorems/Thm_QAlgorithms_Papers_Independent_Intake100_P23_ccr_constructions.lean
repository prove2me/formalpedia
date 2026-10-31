-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P23_ccr_constructions
-- name    : QAlgorithms.Papers.Independent.Intake100.P23.ccr_constructions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:40:56.739549+00:00
-- url     : https://prove2.me/theorems/38c56b05-652b-4575-835f-2cfec3fdc501
-- title:
--   Symplectic pullback and tensor product of CCR representations
-- statement:
--   For $i=1,2$, let $(Y_i,\omega_i)$ be real vector spaces with antisymmetric bilinear forms, and let $W_i:Y_i\to\mathcal U(H_i)$ be Weyl representations on arbitrary complex Hilbert spaces. Every real linear map $r:Y_1\to Y_1$ preserving $\omega_1$ gives a Weyl representation $y\mapsto W_1(ry)$. Moreover, for $\omega_1\oplus\omega_2$ on $Y_1\oplus Y_2$,
--   $$ (y_1,y_2)\longmapsto W_1(y_1)\otimes W_2(y_2) $$
--   is a Weyl representation on the completed Hilbert tensor product $H_1\otimes H_2$.
--   These constructions transport representations without imposing regularity or invertibility of $r$.
-- source:
--   Introduction to representations of the canonical commutation and anticommutation relations, arXiv:math-ph/0511030v2, PDF p. 10, unnumbered ccr-constructions

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P23

open QAlgorithms.Papers.Independent.Renew46.P03 (tensorVector)

variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section CompletedTensor

variable {H1 H2 : Type*}

variable [NormedAddCommGroup H1] [InnerProductSpace ℂ H1] [CompleteSpace H1]

variable [NormedAddCommGroup H2] [InnerProductSpace ℂ H2] [CompleteSpace H2]

/-- PDF p.10, Section 3.1: symplectic pullback and completed tensor construction;
neither regularity nor nondegeneracy is needed. -/
theorem ccr_constructions
    {Y1 Y2 : Type*} [AddCommGroup Y1] [Module ℝ Y1] [AddCommGroup Y2] [Module ℝ Y2]
    (a : Y1 →ₗ[ℝ] Y1 →ₗ[ℝ] ℝ) (b : Y2 →ₗ[ℝ] Y2 →ₗ[ℝ] ℝ)
    (ha : Antisymmetric a) (hb : Antisymmetric b)
    (W1 : Y1 → H1 →L[ℂ] H1) (W2 : Y2 → H2 →L[ℂ] H2)
    (h1 : IsCCR a W1) (h2 : IsCCR b W2) :
    (∀ r : Y1 →ₗ[ℝ] Y1, PreservesWeylForm a r → IsCCR a (fun y => W1 (r y))) ∧
    IsCCR (sumForm a b) (fun y => tensorOperator (W1 y.1) (W2 y.2)) := by sorry

end CompletedTensor

end QAlgorithms.Papers.Independent.Intake100.P23

end
