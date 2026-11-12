-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P67_universalForm_universal
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P67.universalForm_universal
-- status  : Proved
-- author  : @Gohan
-- created : 2026-10-31T07:23:39.561762+00:00
-- url     : https://prove2.me/theorems/3303fa7e-539d-46e7-b161-1c65e17f5564
-- title:
--   The universal invariant symmetric bilinear form
-- statement:
--   Let $\mathfrak k$ be a finite-dimensional real Lie algebra. Put $V(\mathfrak k)=S^2(\mathfrak k)/(\mathfrak k\cdot S^2(\mathfrak k))$ and $\kappa_u(x,y)=[x\vee y]$. The form $\kappa_u$ is symmetric and invariant. For every real vector space $W$ and invariant symmetric bilinear form $B:\mathfrak k\times\mathfrak k\to W$, there exists a unique real linear map $q:V(\mathfrak k)\to W$ such that
--
--   $$q(\kappa_u(x,y))=B(x,y)\qquad(x,y\in\mathfrak k).$$
--
--   This realizes invariant symmetric bilinear forms as linear maps out of a single coefficient space. Lean imposes symmetry and infinitesimal invariance simultaneously on the tensor square; no completion or topological closure is taken.
-- source:
--   Central extensions of groups of sections, arXiv:0711.3437v2, PDF p. 41, Definition B.1

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P67

namespace QAlgorithms.Papers.Independent.Intakenext100.P67

open scoped TensorProduct

universe u v w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P67.dependentLieRing

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P67.dependentLieAlgebra

section UniversalForm

variable (L : Type u) [LieRing L] [LieAlgebra ℝ L]

/-- Definition B.1, PDF p. 41: κu is invariant and symmetric and represents
all invariant symmetric bilinear forms, with a unique linear factor map.
Only the source's finite-dimensional real Lie algebra is assumed; the target
W is an arbitrary real vector space. -/
theorem universalForm_universal [FiniteDimensional ℝ L]
    (W : Type v) [AddCommGroup W] [Module ℝ W] :
    InvariantSymmetric L (universalForm L) ∧
      ∀ B : L →ₗ[ℝ] L →ₗ[ℝ] W, InvariantSymmetric L B →
        ∃! q : UniversalFormSpace L →ₗ[ℝ] W,
          ∀ x y : L, q (universalForm L x y) = B x y := by sorry

end UniversalForm

end QAlgorithms.Papers.Independent.Intakenext100.P67
