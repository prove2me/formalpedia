-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P04_compatible_operator_reduction
-- name    : QAlgorithms.Papers.Independent.Claimed50.P04.compatible_operator_reduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:57:25.226867+00:00
-- url     : https://prove2.me/theorems/fd5bea2b-71ac-4a73-855f-24688ce6ef77
-- title:
--   Remark 3.18: beta-compatible operator reduction
-- statement:
--   Let $\mathfrak g=\mathfrak g(\mathfrak l,V,Z,\beta)$ be finite-dimensional real admissible in its specified structural coordinates. If $(D_V,D_Z)$ is $\beta$-compatible, then $[D_V,X]\in\mathfrak{sp}(V,\beta)$ for every $X\in\mathfrak{sp}(V,\beta)$. Moreover, there exist $E_V\in\mathfrak{sp}(V,\beta)$ and $F_V$ commuting with $[\mathfrak{sp}(V,\beta),\mathfrak{sp}(V,\beta)]$ such that
--   $$D_V=E_V+F_V,\qquad D_Z\beta(v,w)=\beta(F_Vv,w)+\beta(v,F_Vw).$$
--   The derived algebra is the actual span of endomorphism commutators. This reduces compatible operators without assuming the decomposition.
-- source:
--   Lie wedges of endomorphism semigroups of standard subspaces in admissible Lie algebras, arXiv:2007.13445v1, PDF p. 24, Remark 3.18: beta-compatible operator reduction

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

/-- Remark 3.18, PDF p. 24. Both operators E,F are existential CONCLUSIONS and the
remaining pair retains beta-compatibility. -/
theorem compatible_operator_reduction (ha : LieAdmissible (G := G))
    (P : SpindlerPresentation (G := G)) (DV : Module.End ℝ P.V)
    (DZ : Module.End ℝ (LieAlgebra.center ℝ G))
    (hc : ∀ v w : P.V, DZ (spindlerBracket P v w) = spindlerBracket P (DV v) w + spindlerBracket P v (DV w)) :
    (∀ X : Module.End ℝ P.V, PreservesBeta P X →
      PreservesBeta P (DV.comp X - X.comp DV)) ∧
    ∃ E F : Module.End ℝ P.V, DV = E + F ∧ PreservesBeta P E ∧
      (∀ X ∈ derivedSymplectic P, F.comp X = X.comp F) ∧
      (∀ v w : P.V, DZ (spindlerBracket P v w) = spindlerBracket P (F v) w + spindlerBracket P v (F w)) := by sorry

end FurtherStructure

end

end QAlgorithms.Papers.Independent.Claimed50.P04
