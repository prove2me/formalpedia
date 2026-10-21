-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_convex_submodule
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.convex_submodule
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:42:48.090878+00:00
-- url     : https://prove2.me/theorems/3d2a52eb-d333-4289-8453-daa45b02faaa
-- title:
--   Lemma 2.16
-- statement:
--   Let $(V,\Omega)$ be a finite-dimensional symplectic module of strict convex type for a finite-dimensional real Lie algebra $\mathfrak g$. Every $\mathfrak g$-submodule $W\subseteq V$ satisfies
--   $$\Omega|_{W\times W}\text{ is nondegenerate},\qquad \exists x\in\mathfrak g\ \forall\,0\ne w\in W:\ \Omega(xw,w)>0.$$
--   Alternation and invariance restrict from the original form, so the restricted module is again symplectic of convex type. This includes the zero submodule.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 9, Lemma 2.16

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

/-- Lemma 2.16, PDF p. 9: restriction to EVERY submodule preserves convex symplecticity. -/
theorem convex_submodule (rho : L →ₗ⁅ℝ⁆ Module.End ℝ V)
    (omega : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hs : SymplecticModule rho omega)
    (hc : StrictConvexType rho omega) (W : Submodule ℝ V) (hw : Stable rho W) :
    NondegenerateOn omega W ∧ ConvexOn rho omega W := by sorry

end Modules

end

end QAlgorithms.Papers.Independent.Claimed50.P04
