-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_ExistsUnique_of_found_2d171972a414
-- name    : P2M_GroundTheory_Heights__Heights_Targets_ExistsUnique_of_found_2d171972a414
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:49:37.746838+00:00
-- url     : https://prove2.me/theorems/2846a995-29c0-5fd3-89b9-51ef18c373a6
-- title:
--   P2 M Ground Theory Heights  Heights Targets Exists Unique of found 2d171972a414: P2 M Ground Theory Heights  Heights Targets Exists Unique of found 2d171972a414
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Exists Unique of found 2d171972a414 construction uses the P2 M Ground Theory Heights  Heights Targets Exists Unique of found 2d171972a414 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ExistsUnique.lean#L15-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/ExistsUnique.lean#L15-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyBridgeFull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StatementsExistsUniqueRelabel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_ExistsUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR
universe u v w

theorem P2M_GroundTheory_Heights__Heights_Targets_ExistsUnique_of_found_2d171972a414 (hN : IntNumIsFieldIntersection.Statement.{u})
    (hUq : FieldNumbers.IntNumUnique.Statement.{u}) (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (F : Type u) [Field F] {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ExistsUniqueStatement F ι := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«ExistsUnique».«of_found» := P2M_GroundTheory_Heights__Heights_Targets_ExistsUnique_of_found_2d171972a414
