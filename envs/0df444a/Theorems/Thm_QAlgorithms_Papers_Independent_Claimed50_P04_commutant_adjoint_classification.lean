-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_commutant_adjoint_classification
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.commutant_adjoint_classification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:43:41.837501+00:00
-- url     : https://prove2.me/theorems/5877a313-5996-4c4d-a794-499a56e8f5e6
-- title:
--   Proposition 2.18
-- statement:
--   Let $(V,\Omega)$ be a finite-dimensional symplectic module for a finite-dimensional real Lie algebra $\mathfrak g$. The algebra $A=\operatorname{End}_{\mathfrak g}(V)$ is stable under the adjoint determined by $\Omega(Tv,w)=\Omega(v,T^\#w)$. If $V$ is simple and of convex type, there is an algebra isomorphism from $A$ to $\mathbb R$, $\mathbb C$, or $\mathbb H$ carrying $\#$ to identity or the usual conjugation, respectively. In particular,
--   $$\{T\in A:T^\#=T\}=\mathbb R\,\operatorname{id}_V.$$
--   Compatibility is required for a chosen algebra isomorphism. The defining adjoint equation also gives its uniqueness. This describes the real division algebra with its involution.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 9, Proposition 2.18

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P04

namespace QAlgorithms.Papers.Independent.Claimed50.P04

noncomputable section

open Set

attribute [local instance 100] LieRing.ofAssociativeRing

open QAlgorithms.Papers.Independent.Frontier30.P26
  (Invariant LieAdmissible ClosedCone CompactlyEmbedded CompactCartan Hermitian bracketSpan
    TubeType)

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedGroup

attribute [local instance] QAlgorithms.Papers.Independent.Claimed50.P04.lieNormedSpace

section Modules

variable {L V : Type*} [LieRing L] [LieAlgebra ℝ L] [FiniteDimensional ℝ L]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

/-- Proposition 2.18(a),(b), PDF pp. 9–10. The real/complex/quaternionic algebra
isomorphism is CHOSEN compatibly with the involution, not universally quantified.
The adjoint is expressed by its uniquely characterizing form equation. -/
theorem commutant_adjoint_classification (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V)
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : SymplecticModule rho omega) :
    (∀ T : Module.End ℝ V, ModuleEnd rho T →
      ∃! S : Module.End ℝ V, AdjointPair omega T S ∧ ModuleEnd rho S) ∧
    (SimpleModule rho → StrictConvexType rho omega →
      (((∃ e : EndAlgebra rho ≃ₐ[ℝ] ℝ,
          ∀ T S : EndAlgebra rho, AdjointPair omega T S → e S = e T) ∨
        (∃ e : EndAlgebra rho ≃ₐ[ℝ] ℂ,
          ∀ T S : EndAlgebra rho, AdjointPair omega T S → e S = star (e T)) ∨
        (∃ e : EndAlgebra rho ≃ₐ[ℝ] Quaternion ℝ,
          ∀ T S : EndAlgebra rho, AdjointPair omega T S → e S = star (e T))) ∧
      (∀ T : Module.End ℝ V, ModuleEnd rho T →
        (AdjointPair omega T T ↔ ∃ r : ℝ, T = r • LinearMap.id)))) := by sorry

end Modules

end

end QAlgorithms.Papers.Independent.Claimed50.P04
