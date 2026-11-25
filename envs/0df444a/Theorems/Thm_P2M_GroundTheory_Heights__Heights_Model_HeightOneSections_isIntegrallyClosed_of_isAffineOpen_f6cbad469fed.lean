-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_isIntegrallyClosed_of_isAffineOpen_f6cbad469fed
-- name    : P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_isIntegrallyClosed_of_isAffineOpen_f6cbad469fed
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:30:52.782929+00:00
-- url     : https://prove2.me/theorems/6ce1097a-f741-4870-ad0a-9ea21325bc83
-- title:
--   P2 M Ground Theory Heights  Heights Model Height One Sections is Integrally Closed of is Affine Open f6cbad469fed: P2 M Ground Theory Heights  Heights Model Height One Sections is Integrally Closed of
-- statement:
--   The P2 M Ground Theory Heights  Heights Model Height One Sections is Integrally Closed of is Affine Open f6cbad469fed construction uses the P2 M Ground Theory Heights  Heights Model Height One Sections is Integrally Closed of is Affine Open f6cbad469fed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PHeightOneSectionsLocal.lean#L26-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PHeightOneSectionsLocal.lean#L26-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBundlesAgree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PHeightOneSectionsLocal
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
open GroundTheory.Heights₂.Heights.Model.HeightOneSections
variable {X : Scheme.{0}} [IsIntegral X]

theorem P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_isIntegrallyClosed_of_isAffineOpen_f6cbad469fed (hN : IsNormalScheme X) {V : X.Opens}
    (hV : IsAffineOpen V) [Nonempty V] : IsIntegrallyClosed Γ(X, V) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«HeightOneSections».«isIntegrallyClosed_of_isAffineOpen» := P2M_GroundTheory_Heights__Heights_Model_HeightOneSections_isIntegrallyClosed_of_isAffineOpen_f6cbad469fed
