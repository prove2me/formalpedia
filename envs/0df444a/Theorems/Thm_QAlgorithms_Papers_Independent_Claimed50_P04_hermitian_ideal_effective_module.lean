-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_hermitian_ideal_effective_module
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.hermitian_ideal_effective_module
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:41:51.999723+00:00
-- url     : https://prove2.me/theorems/bb070296-1913-4743-857f-ae7e0e5126ee
-- title:
--   Lemma 2.15
-- statement:
--   Let $\mathfrak g$ be a finite-dimensional real quasihermitian reductive Lie algebra, $(V,\Omega)$ a symplectic $\mathfrak g$-module of strict convex type, and $\mathfrak h$ a hermitian simple ideal acting nontrivially. For the restricted representation define $V_0=V^{\mathfrak h}$ and $V_1=\operatorname{span}(\mathfrak h.V)$. Then
--   $$V=V_0\oplus V_1,\qquad \Omega(V_0,V_1)=0.$$
--   Both spaces are $\mathfrak h$-stable, $\mathfrak h.V_0=0$, and the restricted form on $V_1$ is nondegenerate and admits a positive definite Hamiltonian from an element of $\mathfrak h$. Thus $(V_1,\Omega|_{V_1})$ is a symplectic $\mathfrak h$-module of convex type. This identifies the effective summand used in the proof.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 9, Lemma 2.15

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

/-- Lemma 2.15, PDF p. 9: V0 is the h-fixed space and V1=span(h.V), exactly the
constructed spaces in the proof. Positivity uses an element of h itself. -/
theorem hermitian_ideal_effective_module [LieAlgebra.HasCentralRadical ℝ L]
    (hq : Quasihermitian (G := L)) (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V)
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : SymplecticModule rho omega)
    (hc : StrictConvexType rho omega) (H : LieIdeal ℝ L) [LieAlgebra.IsSimple ℝ H]
    (hh : Hermitian (G := H)) (hn : ∃ x : H, ∃ v : V, rho (x : L) v ≠ 0) :
    let rhoH := rho.comp H.incl
    IsCompl (representationFixedSpace rhoH) (representationEffectiveSpace rhoH) ∧
    Stable rhoH (representationFixedSpace rhoH) ∧ Stable rhoH (representationEffectiveSpace rhoH) ∧
    (∀ v ∈ representationFixedSpace rhoH, ∀ w ∈ representationEffectiveSpace rhoH, omega v w = 0) ∧
    (∀ x : H, ∀ v ∈ representationFixedSpace rhoH, rho (x : L) v = 0) ∧
    NondegenerateOn omega (representationEffectiveSpace rhoH) ∧ ConvexOn rhoH omega (representationEffectiveSpace rhoH) := by sorry

end Modules

end

end QAlgorithms.Papers.Independent.Claimed50.P04
