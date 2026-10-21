-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_coadjoint_description
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.coadjoint_description
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:55:20.36913+00:00
-- url     : https://prove2.me/theorems/4194e212-cefa-4a79-8777-99a978d3aa62
-- title:
--   Remark 3.1(a): coadjoint description of W_f
-- statement:
--   Fix a finite-dimensional real admissible Spindler presentation $\mathfrak g=\mathfrak g(\mathfrak l,V,Z,\beta)$ and $f\in Z^*$ whose scalar form is symplectic of strict convex type. Extend $f$ by zero on $V\oplus\mathfrak l$, obtaining $\bar f\in\mathfrak g^*$. Then
--   $$W_f=\{x\in\mathfrak g:\ell(x)\ge0\text{ for every }\ell\in\operatorname{Inn}(\mathfrak g).\bar f\}.$$
--   The orbit uses all finite products of inner exponentials, including inverses. This identifies the fixed pullback cone with the full coadjoint-orbit dual for its specified zero extension.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 15, Remark 3.1(a): coadjoint description of W_f

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

/-- Remark 3.1(a), PDF p. 15: zero extension is fixed before the coadjoint orbit. -/
theorem coadjoint_description (ha : LieAdmissible (G := G))
    (P : SpindlerPresentation (G := G))
    (f : (LieAlgebra.center ℝ G) →ₗ[ℝ] ℝ) (hf : ScalarConvex P f) :
    Wf P f = CoadjointDual P f := by sorry

end LieDefinitions

end

end QAlgorithms.Papers.Independent.Claimed50.P04
