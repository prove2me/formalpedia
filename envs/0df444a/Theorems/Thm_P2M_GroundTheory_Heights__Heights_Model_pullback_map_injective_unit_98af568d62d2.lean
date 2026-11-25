-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_pullback_map_injective_unit_98af568d62d2
-- name    : P2M_GroundTheory_Heights__Heights_Model_pullback_map_injective_unit_98af568d62d2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:31:09.965793+00:00
-- url     : https://prove2.me/theorems/c72044b6-9de2-4bcd-875c-dbf6bc08708f
-- title:
--   P2 M Ground Theory Heights  Heights Model pullback map injective unit 98af568d62d2: P2 M Ground Theory Heights  Heights Model pullback map injective unit 98af568d62d2
-- statement:
--   The P2 M Ground Theory Heights  Heights Model pullback map injective unit 98af568d62d2 construction uses the P2 M Ground Theory Heights  Heights Model pullback map injective unit 98af568d62d2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PPullbackFaithful.lean#L16-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PPullbackFaithful.lean#L16-L36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullbackFaithful
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PPullbackFaithful
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
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
universe u
set_option backward.isDefEq.respectTransparency.types false

theorem P2M_GroundTheory_Heights__Heights_Model_pullback_map_injective_unit_98af568d62d2 {T U : Scheme.{u}} (g : T ⟶ U)
    (hg : ∀ W : U.Opens, Function.Injective (g.app W)) {A : U.Modules}
    (φ₁ φ₂ : A ⟶ structureModule U)
    (h : (Scheme.Modules.pullback g).map φ₁ = (Scheme.Modules.pullback g).map φ₂) : φ₁ = φ₂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«pullback_map_injective_unit» := P2M_GroundTheory_Heights__Heights_Model_pullback_map_injective_unit_98af568d62d2
