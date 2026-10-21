-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_spindler_forward
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.spindler_forward
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:40:59.574851+00:00
-- url     : https://prove2.me/theorems/d27e84fd-88ad-44c6-8ca7-ec498f32fc9f
-- title:
--   Theorem 2.8(a): admissible structural presentation
-- statement:
--   Let $\mathfrak g$ be a finite-dimensional real admissible Lie algebra, $\mathfrak u$ its maximal nilpotent ideal, and $\mathfrak t$ any compactly embedded Cartan subalgebra. Then $[\mathfrak u,\mathfrak u]\subseteq\mathfrak z(\mathfrak g)$ and there exists a reductive $\mathfrak t$-invariant subalgebra $\mathfrak l$ with $V=[\mathfrak t,\mathfrak u]$ such that
--   $$\mathfrak g\cong\mathfrak g(\mathfrak l,V,\mathfrak z(\mathfrak g),\beta),\qquad \beta(v,w)=[v,w].$$
--   The action is the restricted adjoint action and $\beta(xv,w)+\beta(v,xw)=0$. Every element of $\mathfrak t\cap\mathfrak l$ acts semisimply on $V$ with purely imaginary complex spectrum, and the common fixed space is zero. All these data are conclusions. This is the forward structural presentation.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 6, Theorem 2.8(a): admissible structural presentation

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

/-- Theorem 2.8(a), PDF pp. 6–7: t-parametrized forward structure, including equation (2),
semisimplicity, purely imaginary spectrum, and zero tl-fixed space. -/
theorem spindler_forward (ha : LieAdmissible (G := G))
    (U : LieIdeal ℝ G) (hu : MaximalNilpotent U) :
    (∀ u v : U, ⁅(u : G), (v : G)⁆ ∈ LieAlgebra.center ℝ G) ∧
    ∀ T : LieSubalgebra ℝ G, CompactCartan T →
      ∃ P : SpindlerPresentation (G := G),
        P.V = bracketSpan T.toSubmodule U.toSubmodule ∧
        (∀ t : T, ∀ x : P.L, ⁅(t : G), (x : G)⁆ ∈ P.L) ∧
        (∀ x : P.L, ∀ v w : P.V,
          spindlerBracket P (spindlerAction P x v) w + spindlerBracket P v (spindlerAction P x w) = 0) ∧
        (∀ x : P.L, (x : G) ∈ T → Module.End.IsSemisimple (spindlerAction P x) ∧
          ∀ z ∈ ComplexEigenvalues (spindlerAction P x), z.re = 0) ∧
        (∀ v : P.V, (∀ x : P.L, (x : G) ∈ T → spindlerAction P x v = 0) → v = 0) := by sorry

end LieDefinitions

end

end QAlgorithms.Papers.Independent.Claimed50.P04
