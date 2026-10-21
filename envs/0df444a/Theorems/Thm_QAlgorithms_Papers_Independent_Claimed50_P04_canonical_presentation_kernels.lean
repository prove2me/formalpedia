-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_canonical_presentation_kernels
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.canonical_presentation_kernels
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:53:21.386543+00:00
-- url     : https://prove2.me/theorems/670129d0-b6a5-439c-9d2b-4e798e016998
-- title:
--   Remark 2.12: canonical presentation hypotheses
-- statement:
--   Let $\mathfrak g$ be finite-dimensional real admissible with canonical structural data $\mathfrak g=\mathfrak u\rtimes\mathfrak l$, central coordinate $Z=\mathfrak z(\mathfrak g)$, compact Cartan $\mathfrak t_l\subseteq\mathfrak l$, and $V=[\mathfrak t_l,\mathfrak u]$. Then
--   $$V^{\mathfrak t_l}=0,\qquad \{x\in\mathfrak z(\mathfrak l):x.V=0\}=0.$$
--   The second space is the kernel of the center's action, not the space of centrally fixed vectors in $V$. These are the canonical hypotheses needed by the admissibility criterion.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 8, Remark 2.12: canonical presentation hypotheses

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

/-- Remark 2.12, PDF p. 8, for the canonical structural data from Theorem 2.8.
The second kernel is the kernel of the CENTER'S ACTION, not fixed vectors in V. -/
theorem canonical_presentation_kernels (ha : LieAdmissible (G := G))
    (P : SpindlerPresentation (G := G)) (U : LieIdeal ℝ G)
    (hu : MaximalNilpotent U) (hc : Complement U P.L)
    (TL : LieSubalgebra ℝ P.L) (ht : CompactCartan TL)
    (hv : P.V = bracketSpan (TL.map P.L.incl).toSubmodule U.toSubmodule) :
    (∀ v : P.V, (∀ x : P.L, x ∈ TL → spindlerAction P x v = 0) → v = 0) ∧
    (∀ x : LieAlgebra.center ℝ P.L,
      (∀ v : P.V, spindlerAction P (x : P.L) v = 0) → x = 0) := by sorry

end LieDefinitions

end

end QAlgorithms.Papers.Independent.Claimed50.P04
