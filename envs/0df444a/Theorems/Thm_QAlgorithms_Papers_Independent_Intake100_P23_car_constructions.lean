-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P23_car_constructions
-- name    : QAlgorithms.Papers.Independent.Intake100.P23.car_constructions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T16:47:55.207511+00:00
-- url     : https://prove2.me/theorems/474e98c1-9979-432f-878f-036c60524ea3
-- title:
--   Graded tensor and isometric pullback CAR constructions
-- statement:
--   Let $Y_1,Y_2$ be real Hilbert spaces and $H_1,H_2$ complex Hilbert spaces. Suppose $I\in B(H_1)$ is self-adjoint and $(y,t)\mapsto\phi_1(y)+tI$ is a CAR representation of $Y_1\oplus\mathbb R$. Let $\phi_2$ be a CAR representation of $Y_2$. Then
--   $$\Phi(y_1,y_2)=\phi_1(y_1)\otimes1+I\otimes\phi_2(y_2)$$
--   is a CAR representation on the completed $H_1\otimes H_2$, over the Hilbert direct sum $Y_1\oplus Y_2$. In addition, any real linear isometric embedding $r:Y_2\to Y_2$ gives the CAR representation $y\mapsto\phi_2(ry)$.
--   The extended CAR hypothesis supplies both $I^2=1$ and its required anticommutation with the first fields.
-- source:
--   Introduction to representations of the canonical commutation and anticommutation relations, arXiv:math-ph/0511030v2, PDF p. 15, unnumbered car-constructions

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

/-- PDF p.15, Section 4.1: graded tensor CAR and isometric pullback.
The extended CAR supplies I squared equal to one and anticommutation.
WithLp supplies the Hilbert direct sum, rather than the product maximum norm. -/
theorem car_constructions
    {E1 E2 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℝ E1] [CompleteSpace E1]
    [NormedAddCommGroup E2] [InnerProductSpace ℝ E2] [CompleteSpace E2]
    (phi1 : E1 → H1 →L[ℂ] H1) (phi2 : E2 → H2 →L[ℂ] H2) (I : H1 →L[ℂ] H1)
    (hI : star I = I)
    (h1 : IsCAR (fun y : WithLp 2 (E1 × ℝ) => phi1 y.ofLp.1 + y.ofLp.2 • I))
    (h2 : IsCAR phi2) :
    IsCAR (fun y : WithLp 2 (E1 × E2) =>
      tensorOperator (phi1 y.ofLp.1) (1 : H2 →L[ℂ] H2) + tensorOperator I (phi2 y.ofLp.2)) ∧
    (∀ r : E2 →ₗᵢ[ℝ] E2, IsCAR (fun y => phi2 (r y))) := by sorry

end CompletedTensor

end QAlgorithms.Papers.Independent.Intake100.P23

end
