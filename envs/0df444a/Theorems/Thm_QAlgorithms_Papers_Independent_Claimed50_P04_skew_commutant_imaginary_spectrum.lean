-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_skew_commutant_imaginary_spectrum
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.skew_commutant_imaginary_spectrum
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:44:28.195874+00:00
-- url     : https://prove2.me/theorems/82cf3ebe-b702-44b2-b6b5-69dd22ee7fed
-- title:
--   Lemma 2.19
-- statement:
--   Let $(V,\Omega)$ be a finite-dimensional symplectic module of strict convex type for a finite-dimensional real Lie algebra $\mathfrak g$. If $T$ commutes with the representation and satisfies $\Omega(Tv,w)=-\Omega(v,Tw)$, then
--   $$\operatorname{spec}(T_{\mathbb C})\subseteq i\mathbb R.$$
--   Here $T_{\mathbb C}$ is the actual complexification of the real linear endomorphism. This rules out nonimaginary eigenvalues in the skew-adjoint commutant.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 10, Lemma 2.19

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

/-- Lemma 2.19, PDF p. 10: the -# condition is its defining form equation;
the spectral condition concerns the complexification, not the real spectrum. -/
theorem skew_commutant_imaginary_spectrum (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V)
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : SymplecticModule rho omega)
    (hc : StrictConvexType rho omega) (T : Module.End ℝ V) (ht : ModuleEnd rho T)
    (hskew : ∀ v w, omega (T v) w = -omega v (T w)) :
    ∀ z ∈ ComplexEigenvalues T, z.re = 0 := by sorry

end Modules

end

end QAlgorithms.Papers.Independent.Claimed50.P04
