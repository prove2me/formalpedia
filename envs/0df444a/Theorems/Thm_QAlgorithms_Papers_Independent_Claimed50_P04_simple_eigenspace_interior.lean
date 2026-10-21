-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_simple_eigenspace_interior
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.simple_eigenspace_interior
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:51:48.49404+00:00
-- url     : https://prove2.me/theorems/ba2838a3-a431-4804-87cf-0b9324d7238f
-- title:
--   Lemma 3.16
-- statement:
--   Let $\mathfrak g=\mathfrak g(\mathfrak s,V,Z,\beta)$ be a finite-dimensional real admissible Lie algebra with $\mathfrak s$ hermitian simple of tube type. Let $f\in Z^*$ make $f\circ\beta$ symplectic of strict convex type. For a nonzero three-grading element $h\in\mathfrak s$ and either $\lambda\in\{-1,1\}$, there exists $x\in\mathfrak s_\lambda(h)\cap W_f$ such that
--   $$x+z\in\operatorname{int}_{\mathfrak g_\lambda}(W_f\cap\mathfrak g_\lambda)\quad\text{for every }z\in Z\text{ with }f(z)>0,$$
--   where $\mathfrak g_\lambda=V_{\lambda/2}(\rho(h))\oplus Z\oplus\mathfrak s_\lambda(h)$ is the specified auxiliary subspace. This gives a common interior witness for all positive central translates.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 23, Lemma 3.16

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

section LieDefinitions

variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

/-- Lemma 3.16, PDF p. 23. The interior lives in the specified AUXILIARY SUBSPACE.
x is chosen before all central z with f(z)>0. -/
theorem simple_eigenspace_interior (ha : LieAdmissible (G := G))
    (P : SpindlerPresentation (G := G)) [LieAlgebra.IsSimple ℝ P.L]
    (hh : Hermitian (G := P.L)) (ht : TubeType (G := P.L))
    (f : (LieAlgebra.center ℝ G) →ₗ[ℝ] ℝ) (hf : ScalarConvex P f)
    (h : P.L) (hne : h ≠ 0) (hg : ThreeGraded (LieAlgebra.ad ℝ P.L h)) :
    ∀ lam : ℝ, (lam = -1 ∨ lam = 1) →
      ∃ x : P.L, ⁅h, x⁆ = lam • x ∧ (x : G) ∈ Wf P f ∧
        ∀ z : LieAlgebra.center ℝ G, 0 < f z →
          ∃ y : ↥((P.V ⊓ Module.End.eigenspace (LieAlgebra.ad ℝ G (h : G)) (lam / 2)) ⊔
              (LieAlgebra.center ℝ G).toSubmodule ⊔
              ((Module.End.eigenspace (LieAlgebra.ad ℝ P.L h) lam).map P.L.incl.toLinearMap)),
            (y : G) = (x : G) + (z : G) ∧
            y ∈ interior (Subtype.val ⁻¹' Wf P f) := by sorry

end LieDefinitions

end

end QAlgorithms.Papers.Independent.Claimed50.P04
