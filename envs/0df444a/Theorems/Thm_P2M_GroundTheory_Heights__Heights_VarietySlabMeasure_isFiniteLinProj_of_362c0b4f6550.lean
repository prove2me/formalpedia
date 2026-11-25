-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarietySlabMeasure_isFiniteLinProj_of_362c0b4f6550
-- name    : P2M_GroundTheory_Heights__Heights_VarietySlabMeasure_isFiniteLinProj_of_362c0b4f6550
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:11.552201+00:00
-- url     : https://prove2.me/theorems/46c243e5-4529-4dfb-a580-5e3cb673155f
-- title:
--   P2 M Ground Theory Heights  Heights Variety Slab Measure is Finite Lin Proj of 362c0b4f6550: P2 M Ground Theory Heights  Heights Variety Slab Measure is Finite Lin Proj of 362c0b4f6550
-- statement:
--   The P2 M Ground Theory Heights  Heights Variety Slab Measure is Finite Lin Proj of 362c0b4f6550 construction uses the P2 M Ground Theory Heights  Heights Variety Slab Measure is Finite Lin Proj of 362c0b4f6550 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietySlabMeasure.lean#L22-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietySlabMeasure.lean#L22-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietySlabMeasure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StVarietyProjectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteProjectionsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RingKrullDimQuotBotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_AffineOfCone
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNullSmaller
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PVarietySlabMeasure
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
open MvPolynomial MeasureTheory
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.VarietySlabMeasure

theorem P2M_GroundTheory_Heights__Heights_VarietySlabMeasure_isFiniteLinProj_of_362c0b4f6550 {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (h : ComplexSets.IsFiniteProjection J A) :
    IsFiniteLinProj J A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarietySlabMeasure».«isFiniteLinProj_of» := P2M_GroundTheory_Heights__Heights_VarietySlabMeasure_isFiniteLinProj_of_362c0b4f6550
