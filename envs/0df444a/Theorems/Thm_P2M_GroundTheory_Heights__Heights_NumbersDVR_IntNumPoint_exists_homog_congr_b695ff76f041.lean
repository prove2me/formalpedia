-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_exists_homog_congr_b695ff76f041
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_exists_homog_congr_b695ff76f041
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:11.3915+00:00
-- url     : https://prove2.me/theorems/ef47e67e-c24f-439d-a029-9005e623146a
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point exists homog congr b695ff76f041: P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point exists homog congr b695ff76f041
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point exists homog congr b695ff76f041 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Int Num Point exists homog congr b695ff76f041 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L46-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PIntNumPoint.lean#L46-L71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsBridge
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.NumbersDVR.IntNumPoint
variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_exists_homog_congr_b695ff76f041 (i : ∀ k, ι k) (p : MRing ι F) :
    ∃ N : K → ℕ, ∀ N', N ≤ N' → ∃ h : MRing ι F, IsMultiHomog h N' ∧
      Ideal.Quotient.mk (chartUnitIdeal i) p = Ideal.Quotient.mk (chartUnitIdeal i) h := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«IntNumPoint».«exists_homog_congr» := P2M_GroundTheory_Heights__Heights_NumbersDVR_IntNumPoint_exists_homog_congr_b695ff76f041
