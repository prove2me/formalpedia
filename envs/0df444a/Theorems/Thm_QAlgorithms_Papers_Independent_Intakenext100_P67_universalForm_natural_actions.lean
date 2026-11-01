-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakenext100_P67_universalForm_natural_actions
-- name    : QAlgorithms.Papers.Independent.Intakenext100.P67.universalForm_natural_actions
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-31T07:24:39.183+00:00
-- url     : https://prove2.me/theorems/d0499064-c62a-4701-a3a5-156e45c37dca
-- title:
--   Natural automorphism and derivation actions
-- statement:
--   Let $\mathfrak k$ be a finite-dimensional real Lie algebra. Its automorphism group and derivation Lie algebra act naturally on $V(\mathfrak k)$. Their representations $A$ and $d$ are determined by
--
--   $$A(\phi)\kappa_u(x,y)=\kappa_u(\phi x,\phi y),\qquad d(D)\kappa_u(x,y)=\kappa_u(Dx,y)+\kappa_u(x,Dy).$$
--
--   Every inner derivation acts as zero. If all derivations are inner, then $\operatorname{Aut}(\mathfrak k)_0$ acts trivially on $V(\mathfrak k)$; this also holds for semisimple $\mathfrak k$. The automorphism topology is the usual finite-dimensional topology, expressed by pointwise evaluation on the Hausdorff real topological vector space $\mathfrak k$.
--
--   These actions control coefficient monodromy in the paper. The representations, action laws and generator formulas are conclusions, not assumed data.
-- source:
--   Central extensions of groups of sections, arXiv:0711.3437v2, PDF p. 41, Remark B.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P67

namespace QAlgorithms.Papers.Independent.Intakenext100.P67

open scoped TensorProduct

universe u v w

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P67.dependentLieRing

attribute [local instance] QAlgorithms.Papers.Independent.Intakenext100.P67.dependentLieAlgebra

section NaturalActions

variable (L : Type u) [LieRing L] [LieAlgebra ℝ L]

attribute [local instance] LieRing.ofAssociativeRing

/-- Remark B.3, PDF p. 41: natural automorphism and derivation representations
on the constructed V(L), their formulas on generators, and triviality of
inner derivations. If all derivations are inner, the identity component of
Aut(L) acts trivially; this also applies to semisimple L. The Hausdorff topological
real vector space L has the unique finite-dimensional vector-space topology.
The action and representation are conclusions, not supplied hypotheses. -/
theorem universalForm_natural_actions
    [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L]
    [T2Space L] [FiniteDimensional ℝ L] :
    letI : TopologicalSpace (L ≃ₗ⁅ℝ⁆ L) := automorphismTopology L
    ∃ (A : (L ≃ₗ⁅ℝ⁆ L) → (UniversalFormSpace L ≃ₗ[ℝ] UniversalFormSpace L))
      (d : LieDerivation ℝ L L →ₗ⁅ℝ⁆ Module.End ℝ (UniversalFormSpace L)),
      (A (1 : L ≃ₗ⁅ℝ⁆ L) = LinearEquiv.refl ℝ (UniversalFormSpace L)) ∧
      (∀ a b, A (a.trans b) = (A a).trans (A b)) ∧
      (∀ a x y, A a (universalForm L x y) = universalForm L (a x) (a y)) ∧
      (∀ D x y, d D (universalForm L x y) =
        universalForm L (D x) y + universalForm L x (D y)) ∧
      (∀ x, d (LieDerivation.inner ℝ L L x) = 0) ∧
      (((∀ D : LieDerivation ℝ L L, ∃ x : L, D = LieDerivation.inner ℝ L L x) ∨
          LieAlgebra.IsSemisimple ℝ L) →
        ∀ a ∈ connectedComponent (1 : L ≃ₗ⁅ℝ⁆ L),
          A a = LinearEquiv.refl ℝ (UniversalFormSpace L)) := by sorry

end NaturalActions

end QAlgorithms.Papers.Independent.Intakenext100.P67
