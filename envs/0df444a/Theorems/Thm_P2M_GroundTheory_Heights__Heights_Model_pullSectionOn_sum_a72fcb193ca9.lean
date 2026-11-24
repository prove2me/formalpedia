-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_sum_a72fcb193ca9
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_sum_a72fcb193ca9
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:25:22.902633+00:00
-- url     : https://prove2.me/theorems/6df6fb77-5a9f-42ab-8513-cf2df48f62bf
-- title:
--   P2 M Ground Theory Heights  Heights Model pull Section On sum a72fcb193ca9: P2 M Ground Theory Heights  Heights Model pull Section On sum a72fcb193ca9
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pull Section On sum a72fcb193ca9 construction uses the P2 M Ground Theory Heights  Heights Model pull Section On sum a72fcb193ca9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L72-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PClearDenominators.lean#L72-L75

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PullbackBasis
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_RatLocalAffine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable {T Z : Scheme.{0}} (g : T ⟶ Z) (M : Z.Modules)

theorem P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_sum_a72fcb193ca9 (U : Z.Opens) {n : ℕ} (t : Fin n → Γ(M, U)) (r : Fin n → Γ(Z, U)) :
    pullSectionOn g M U (∑ i, r i • t i) = ∑ i, g.app U (r i) • pullSectionOn g M U (t i) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullSectionOn_sum» := P2M_GroundTheory_Heights__Heights_Model_pullSectionOn_sum_a72fcb193ca9
