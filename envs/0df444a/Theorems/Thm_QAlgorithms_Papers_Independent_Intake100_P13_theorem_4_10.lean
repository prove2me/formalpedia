-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P13_theorem_4_10
-- name    : QAlgorithms.Papers.Independent.Intake100.P13.theorem_4_10
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T13:10:41.617+00:00
-- url     : https://prove2.me/theorems/fd39d224-9093-4a31-bd72-a5d36f230cf5
-- title:
--   Theorem 4.10
-- statement:
--   Let $V$ be a Hausdorff barrelled real locally convex space, let $\Omega\subseteq V$ be open and convex, and let $f:\Omega\to\mathbb R$ be lower semicontinuous and convex. Then
--   $$
--   f\text{ is continuous on }\Omega.
--   $$
--   The empty domain is allowed. No normability, metrizability, completeness, or finite dimensionality is assumed.
--
--   This extends the continuity property of lower semicontinuous seminorms on barrelled spaces to convex functions on open domains.
--
--   **Source correction.** The printed theorem omits convexity of $f$; the sentence introducing the theorem and its proof require it. The formal statement includes this missing hypothesis.
-- source:
--   A complex semigroup approach to group algebras of infinite dimensional Lie groups, arXiv:0709.1062v1, PDF p. 28, Theorem 4.10

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P13

namespace QAlgorithms.Papers.Independent.Intake100.P13

open Set Filter Topology

noncomputable section

universe u v w

section DualGeometry

variable {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

variable [IsTopologicalAddGroup V] [ContinuousSMul ℝ V]

variable [LocallyConvexSpace ℝ V] [T2Space V]

/-- Theorem 4.10, PDF p. 28. SOURCE CORRECTION: the printed sentence
omits convexity of f. We add ConvexOn, as required by the preceding
sentence (general convex functions), the proof, and Proposition 4.8.
Lower semicontinuity alone is false: f(0)=0, f(t)=1 for t != 0 on R. -/
theorem theorem_4_10
    [BarrelledSpace ℝ V] (Omega : Set V) (hOpen : IsOpen Omega)
    (hConvex : Convex ℝ Omega) (f : V → ℝ)
    (hFunctionConvex : ConvexOn ℝ Omega f)
    (hLower : LowerSemicontinuousOn f Omega) :
    ContinuousOn f Omega := by sorry

end DualGeometry

end

end QAlgorithms.Papers.Independent.Intake100.P13
