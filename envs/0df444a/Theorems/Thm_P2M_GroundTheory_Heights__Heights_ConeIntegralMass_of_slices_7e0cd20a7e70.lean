-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeIntegralMass_of_slices_7e0cd20a7e70
-- name    : P2M_GroundTheory_Heights__Heights_ConeIntegralMass_of_slices_7e0cd20a7e70
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:17:03.388503+00:00
-- url     : https://prove2.me/theorems/bbf621d8-d3c9-4b34-8274-e2857cf90abf
-- title:
--   P2 M Ground Theory Heights  Heights Cone Integral Mass of slices 7e0cd20a7e70: P2 M Ground Theory Heights  Heights Cone Integral Mass of slices 7e0cd20a7e70
-- statement:
--   The P2 M Ground Theory Heights  Heights Cone Integral Mass of slices 7e0cd20a7e70 construction uses the P2 M Ground Theory Heights  Heights Cone Integral Mass of slices 7e0cd20a7e70 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMassFromLelong.lean#L13-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PMassFromLelong.lean#L13-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSectionHyperplaneAvoid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSectionDegreeSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPointSliceMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PMassFromLelong
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_ConeIntegralMass_of_slices_7e0cd20a7e70 (hCP : ConeToProjective.Statement)
    (hS : SliceSectionMass.Statement) (hA : SectionHyperplaneAvoid.Statement)
    (hD : SectionDegreeSum.Statement) (hP : PointSliceMass.Statement) :
    ConeIntegralMass.Statement := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ConeIntegralMass».«of_slices» := P2M_GroundTheory_Heights__Heights_ConeIntegralMass_of_slices_7e0cd20a7e70
