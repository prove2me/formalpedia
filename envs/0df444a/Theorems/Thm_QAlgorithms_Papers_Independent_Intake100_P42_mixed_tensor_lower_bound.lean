-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P42_mixed_tensor_lower_bound
-- name    : QAlgorithms.Papers.Independent.Intake100.P42.mixed_tensor_lower_bound
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T12:25:54.191723+00:00
-- url     : https://prove2.me/theorems/ee03014d-e850-4ac7-ab70-ba181711e32c
-- title:
--   Lower bound for a bounded mixed tensor map
-- statement:
--   Let $\alpha$ be a uniform crossnorm family over the common real or complex field, and $\beta$ a reasonable crossnorm family on all normed pairs. Assume, as an additional global requirement, that every bounded $A:X\to V$ and $B:Y\to W$ gives a bounded tensor map $X\otimes_\alpha Y\to V\otimes_\beta W$. For any such spaces and selected maps, this induced norm is finite and
--
--   $$\|A\|\,\|B\|\le\|A\otimes B\|_{[\alpha,\beta]}=\rho_{\alpha,\beta}(A\otimes B).$$
--
--   Here the middle expression is the actual operator norm of $x\otimes y\mapsto Ax\otimes By$, and the last is its pullback along the canonical operator-tensor action. The assertion supplies only the lower bound; it does not assert equality to the product of the factor norms or a joint metric mapping property.
-- source:
--   Restriction of Uniform Crossnorms, arXiv:2212.10780v2, PDF p. 8, Remark 4.5: lower operator-norm bound for a bounded mixed tensor map

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P42

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P42

open scoped TensorProduct ENNReal

open QAlgorithms.Papers.Independent.Next46.P02

universe u

variable {F : Type u} [RCLike F]

/-- PDF p.8, Remark 4.5: only the lower bound for mixed bounded simple maps.
Global mixed boundedness is the source's EXTRA assumption; no upper mapping
constant, joint uniformity, or equality to the product of factor norms is added. -/
theorem mixed_tensor_lower_bound (a : CrossnormFamily F) (ha : IsUniform a)
    (b : CrossnormFamily F) (hab : MixedBounded a b)
    (X Y V W : Type u)
    [NormedAddCommGroup X] [NormedSpace F X]
    [NormedAddCommGroup Y] [NormedSpace F Y]
    [NormedAddCommGroup V] [NormedSpace F V]
    [NormedAddCommGroup W] [NormedSpace F W]
    (A : X →L[F] V) (B : Y →L[F] W) :
    extendedOperatorNorm (a.norm X Y) (b.norm V W)
        (TensorProduct.map A.toLinearMap B.toLinearMap) < ⊤ ∧
    ‖A‖ * ‖B‖ ≤ algebraicMapNorm (a.norm X Y) (b.norm V W)
      (TensorProduct.map A.toLinearMap B.toLinearMap) ∧
    algebraicMapNorm (a.norm X Y) (b.norm V W)
        (TensorProduct.map A.toLinearMap B.toLinearMap) =
      restrictedOperatorNorm (a.norm X Y) (b.norm V W) (A ⊗ₜ[F] B) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P42

end
