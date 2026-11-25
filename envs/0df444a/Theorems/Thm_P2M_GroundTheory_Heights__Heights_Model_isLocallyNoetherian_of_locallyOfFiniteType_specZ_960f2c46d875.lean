-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isLocallyNoetherian_of_locallyOfFiniteType_specZ_960f2c46d875
-- name    : P2M_GroundTheory_Heights__Heights_Model_isLocallyNoetherian_of_locallyOfFiniteType_specZ_960f2c46d875
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:33.012926+00:00
-- url     : https://prove2.me/theorems/216d02ad-a1a1-436b-916e-fc314a1eb8d6
-- title:
--   P2 M Ground Theory Heights  Heights Model is Locally Noetherian of locally Of Finite Type spec Z 960f2c46d875: P2 M Ground Theory Heights  Heights Model is Locally Noetherian of locally Of Finite Type
-- statement:
--   The P2 M Ground Theory Heights  Heights Model is Locally Noetherian of locally Of Finite Type spec Z 960f2c46d875 construction uses the P2 M Ground Theory Heights  Heights Model is Locally Noetherian of locally Of Finite Type spec Z 960f2c46d875 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PInvOpenInsideRat.lean#L12-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/IntegralModels/PInvOpenInsideRat.lean#L12-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsInvOpenInsideRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PInvOpenInsideRat
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

theorem P2M_GroundTheory_Heights__Heights_Model_isLocallyNoetherian_of_locallyOfFiniteType_specZ_960f2c46d875 {X : Scheme.{0}} (f : X ⟶ SpecZ)
    [LocallyOfFiniteType f] : IsLocallyNoetherian X := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Model».«isLocallyNoetherian_of_locallyOfFiniteType_specZ» := P2M_GroundTheory_Heights__Heights_Model_isLocallyNoetherian_of_locallyOfFiniteType_specZ_960f2c46d875
