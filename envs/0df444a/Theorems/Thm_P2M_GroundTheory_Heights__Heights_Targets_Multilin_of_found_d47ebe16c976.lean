-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Multilin_of_found_d47ebe16c976
-- name    : P2M_GroundTheory_Heights__Heights_Targets_Multilin_of_found_d47ebe16c976
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:42:03.223897+00:00
-- url     : https://prove2.me/theorems/7c323810-48de-5229-b367-93e842d35a7e
-- title:
--   P2 M Ground Theory Heights  Heights Targets Multilin of found d47ebe16c976: P2 M Ground Theory Heights  Heights Targets Multilin of found d47ebe16c976
-- statement:
--   The P2 M Ground Theory Heights  Heights Targets Multilin of found d47ebe16c976 construction uses the P2 M Ground Theory Heights  Heights Targets Multilin of found d47ebe16c976 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/Multilin.lean#L14-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/Multilin.lean#L14-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsFieldIntersectionExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_AssemblyBridgeFull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_Multilin
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights.NumbersDVR
universe u

theorem P2M_GroundTheory_Heights__Heights_Targets_Multilin_of_found_d47ebe16c976
    (hBase : FieldNumbers.IntNumBase.Statement.{u})
    (hCut : FieldNumbers.CutRational.Statement.{u})
    (hEx : FieldNumbers.ExistsForm.Statement.{u})
    (hDiv : FieldNumbers.DivCycleSupport.Statement.{u})
    (hAdd : FieldNumbers.IntNumAdd.Statement.{u})
    {K : Type} [Fintype K] (F : Type u) [Field F] (ι : K → Type) [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.MultilinStatement F ι := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Targets».«Multilin».«of_found» := P2M_GroundTheory_Heights__Heights_Targets_Multilin_of_found_d47ebe16c976
