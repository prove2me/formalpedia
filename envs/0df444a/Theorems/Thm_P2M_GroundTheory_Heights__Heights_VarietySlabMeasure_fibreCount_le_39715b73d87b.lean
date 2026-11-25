-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_VarietySlabMeasure_fibreCount_le_39715b73d87b
-- name    : P2M_GroundTheory_Heights__Heights_VarietySlabMeasure_fibreCount_le_39715b73d87b
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:18.048792+00:00
-- url     : https://prove2.me/theorems/5a0dedb3-8ed0-4be4-adc2-69b1a105f8c9
-- title:
--   P2 M Ground Theory Heights  Heights Variety Slab Measure fibre Count le 39715b73d87b: P2 M Ground Theory Heights  Heights Variety Slab Measure fibre Count le 39715b73d87b
-- statement:
--   The P2 M Ground Theory Heights  Heights Variety Slab Measure fibre Count le 39715b73d87b construction uses the P2 M Ground Theory Heights  Heights Variety Slab Measure fibre Count le 39715b73d87b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietySlabMeasure.lean#L27-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PVarietySlabMeasure.lean#L27-L41

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

theorem P2M_GroundTheory_Heights__Heights_VarietySlabMeasure_fibreCount_le_39715b73d87b {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) {U : Matrix (Fin n) (Fin n) ℂ}
    {s : Fin d → Fin n} (hA : ComplexSets.IsFiniteProjection J (U.submatrix s id))
    (B : Set (EuclideanSpace ℂ (Fin n))) (x : EuclideanSpace ℂ (Fin d)) :
    {z | z ∈ zeroSetEuc J ∩ B ∧ rowsProj U s z = x}.encard ≤
      ComplexSets.projDegree J (U.submatrix s id) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«VarietySlabMeasure».«fibreCount_le» := P2M_GroundTheory_Heights__Heights_VarietySlabMeasure_fibreCount_le_39715b73d87b
