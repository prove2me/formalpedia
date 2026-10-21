-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_nondegeneration
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.nondegeneration
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:52:48.712188+00:00
-- url     : https://prove2.me/theorems/8fa352d2-d041-4350-9e3d-482cfd707f54
-- title:
--   Theorem 3.17 (Non-degeneration Theorem); precise result selected for the seed
-- statement:
--   Let $\mathfrak g=\mathfrak g(\mathfrak l,V,Z,\beta)$ be a finite-dimensional real admissible Lie algebra with a specified structural presentation. Let $f\in Z^*$ make $(V,f\circ\beta)$ a symplectic $\mathfrak l$-module of strict convex type. Define $W_f$ by the nonnegativity, for every $a\in V$, of $\tfrac12 f(\beta(xa,a))+f(\beta(v,a))+f(z)$ at $(v,z,x)$. Every derivation $D$ inducing a three-grading satisfies
--   $$\operatorname{span}(W_f\cap\mathfrak g_\lambda(D))=\mathfrak g_\lambda(D)\qquad(\lambda\in\{-1,1\}).$$
--   The original presentation and cone remain fixed; $D$ need not preserve them. This is the paper's main Non-degeneration Theorem.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 23, Theorem 3.17 (Non-degeneration Theorem); precise result selected for the seed

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

/-- Theorem 3.17 (Non-degeneration), PDF pp. 23–24. The arbitrary derivation need NOT
preserve the specified presentation; the ORIGINAL cone is used for both signs. -/
theorem nondegeneration (ha : LieAdmissible (G := G))
    (P : SpindlerPresentation (G := G)) (D : LieDerivation ℝ G G)
    (hd : ThreeGraded D.toLinearMap)
    (f : (LieAlgebra.center ℝ G) →ₗ[ℝ] ℝ) (hf : ScalarConvex P f) :
    ∀ lam : ℝ, (lam = -1 ∨ lam = 1) →
      Submodule.span ℝ (Wf P f ∩ (Module.End.eigenspace D.toLinearMap lam : Set G)) =
        Module.End.eigenspace D.toLinearMap lam := by sorry

end LieDefinitions

end

end QAlgorithms.Papers.Independent.Claimed50.P04
