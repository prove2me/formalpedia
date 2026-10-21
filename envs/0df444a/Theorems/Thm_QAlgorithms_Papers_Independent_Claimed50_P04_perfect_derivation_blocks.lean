-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_perfect_derivation_blocks
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.perfect_derivation_blocks
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T08:50:59.629061+00:00
-- url     : https://prove2.me/theorems/6df0fa28-20f1-4012-b4e8-4e540a0a5ca2
-- title:
--   Lemma 3.13
-- statement:
--   Let $\mathfrak g=\mathfrak g(\mathfrak s,V,Z,\beta)$ be a finite-dimensional perfect real admissible Lie algebra with its specified structural presentation. A derivation annihilating $\mathfrak s$ has the form
--   $$D(v,z,x)=(D_Vv,D_Zz,0),\qquad D_V\in\operatorname{End}_{\mathfrak s}(V),\quad D_Z\beta(v,w)=\beta(D_Vv,w)+\beta(v,D_Vw).$$
--   Conversely, every compatible pair with $D_V$ commuting with the action defines exactly this derivation and annihilates $\mathfrak s$. The block operator is constructed from the fixed coordinates. This is a two-direction characterization.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 20, Lemma 3.13

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

/-- Lemma 3.13, PDF p. 20. Perfectness is explicit, and the converse constructs a
Lie derivation with precisely the displayed diagonal-block linear map. -/
theorem perfect_derivation_blocks (ha : LieAdmissible (G := G))
    (P : SpindlerPresentation (G := G))
    (hp : LieAlgebra.derivedSeries ℝ G 1 = ⊤) :
    (∀ D : LieDerivation ℝ G G, (∀ x : P.L, D (x : G) = 0) →
      ∃ DV : Module.End ℝ P.V, ∃ DZ : Module.End ℝ (LieAlgebra.center ℝ G),
        D.toLinearMap = blockEnd P DV DZ ∧
        (∀ x : P.L, ∀ v : P.V, DV (spindlerAction P x v) = spindlerAction P x (DV v)) ∧
        (∀ v w : P.V, DZ (spindlerBracket P v w) = spindlerBracket P (DV v) w + spindlerBracket P v (DV w))) ∧
    (∀ DV : Module.End ℝ P.V, ∀ DZ : Module.End ℝ (LieAlgebra.center ℝ G),
      (∀ x : P.L, ∀ v : P.V, DV (spindlerAction P x v) = spindlerAction P x (DV v)) →
      (∀ v w : P.V, DZ (spindlerBracket P v w) = spindlerBracket P (DV v) w + spindlerBracket P v (DV w)) →
      ∃ D : LieDerivation ℝ G G, D.toLinearMap = blockEnd P DV DZ ∧
        ∀ x : P.L, D (x : G) = 0) := by sorry

end FurtherStructure

end

end QAlgorithms.Papers.Independent.Claimed50.P04
