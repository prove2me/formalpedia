-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_faithful_action_reduction
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.faithful_action_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:56:23.840875+00:00
-- url     : https://prove2.me/theorems/2b04cafc-1747-40c5-bc3f-bbb21ce1ef87
-- title:
--   Remark 3.3(b): faithful action reduction
-- statement:
--   Let $\mathfrak g=\mathfrak g(\mathfrak l,V,Z,\beta)$ be finite-dimensional real admissible in structural coordinates. Put $\mathfrak l_{\mathrm{fix}}=\{x\in\mathfrak l:x.V=0\}$. There is a complementary ideal $\mathfrak l_{\mathrm{eff}}$ of $\mathfrak l$ such that
--   $$\mathfrak g=\mathfrak g(\mathfrak l_{\mathrm{eff}},V,Z,\beta)\oplus\mathfrak l_{\mathrm{fix}}.$$
--   The effective ideal acts faithfully on $V$, and the ineffective ideal is reductive and admissible. The summands are actual complementary ideals of the ambient algebra. This removes only the kernel of the action.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 16, Remark 3.3(b): faithful action reduction

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

section FurtherStructure

variable {G : Type*} [LieRing G] [LieAlgebra ℝ G] [FiniteDimensional ℝ G]

/-- Remark 3.3(b), PDF p. 16. The ineffective ideal is defined by its actual action;
the complementary ideal and faithful action on V are conclusions. -/
theorem faithful_action_reduction (ha : LieAdmissible (G := G))
    (P : SpindlerPresentation (G := G)) :
    ∃ I J : LieIdeal ℝ P.L,
      (∀ x : P.L, x ∈ I ↔ ∀ v : P.V, spindlerAction P x v = 0) ∧
      IsCompl I.toSubmodule J.toSubmodule ∧
      (∀ x : J, (∀ v : P.V, spindlerAction P (x : P.L) v = 0) → x = 0) ∧
      LieAlgebra.HasCentralRadical ℝ I ∧ LieAdmissible (G := I) ∧
      ∃ IG N : LieIdeal ℝ G,
        IG.toSubmodule = I.toSubmodule.map P.L.incl.toLinearMap ∧
        N.toSubmodule = P.V ⊔ (LieAlgebra.center ℝ G).toSubmodule ⊔
          J.toSubmodule.map P.L.incl.toLinearMap ∧
        IsCompl IG.toSubmodule N.toSubmodule := by sorry

end FurtherStructure

end

end QAlgorithms.Papers.Independent.Claimed50.P04
