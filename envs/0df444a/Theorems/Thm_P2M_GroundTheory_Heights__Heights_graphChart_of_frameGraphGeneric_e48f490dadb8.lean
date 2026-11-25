-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_graphChart_of_frameGraphGeneric_e48f490dadb8
-- name    : P2M_GroundTheory_Heights__Heights_graphChart_of_frameGraphGeneric_e48f490dadb8
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:46:58.102644+00:00
-- url     : https://prove2.me/theorems/4dd80ef6-83d3-462d-86dc-a1d542aa00c2
-- title:
--   P2 M Ground Theory Heights  Heights graph Chart of frame Graph Generic e48f490dadb8: P2 M Ground Theory Heights  Heights graph Chart of frame Graph Generic e48f490dadb8
-- statement:
--   The P2 M Ground Theory Heights  Heights graph Chart of frame Graph Generic e48f490dadb8 construction uses the P2 M Ground Theory Heights  Heights graph Chart of frame Graph Generic e48f490dadb8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RingKrullDimQuotientMinimalPrimeAddOne.lean#L98-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/RingKrullDimQuotientMinimalPrimeAddOne.lean#L98-L159

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StDivisorGoodPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StFrameGraphGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegularOffHypersurface
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_RingKrullDimQuotientMinimalPrimeAddOne
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
open MvPolynomial Filter Topology ComplexSets
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_graphChart_of_frameGraphGeneric_e48f490dadb8 (hG : FrameGraphGeneric.Statement) {n e : ℕ}
    (W : Ideal (MvPolynomial (Fin n) ℂ)) (hW : W.IsPrime)
    (he : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = e) :
    ∃ h : MvPolynomial (Fin n) ℂ, h ∉ W ∧ ∀ z ∈ zeroSet W, eval z h ≠ 0 →
      ∃ (A : (Fin n → ℂ) →L[ℂ] (Fin e → ℂ)) (O : Set (Fin e → ℂ)) (V : Set (Fin n → ℂ))
        (g : (Fin e → ℂ) → Fin n → ℂ), IsOpen O ∧ IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ g O ∧
          (∀ y ∈ O, A (g y) = y) ∧ zeroSet W ∩ V = g '' O := by sorry

alias «GroundTheory».«Heights₂».«Heights».«graphChart_of_frameGraphGeneric» := P2M_GroundTheory_Heights__Heights_graphChart_of_frameGraphGeneric_e48f490dadb8
