-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_projIdx_e108999e94b3
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_projIdx_e108999e94b3
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:01:54.922728+00:00
-- url     : https://prove2.me/theorems/a1df280b-f5a1-4eee-87c5-30d15c8a1ef9
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers weight proj Idx e108999e94b3: P2 M Ground Theory Heights  Heights Field Numbers weight proj Idx e108999e94b3
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers weight proj Idx e108999e94b3 construction uses the P2 M Ground Theory Heights  Heights Field Numbers weight proj Idx e108999e94b3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/StatementsExamples.lean#L50-L53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsExamples
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_projIdx_e108999e94b3 (N : ℕ) (d : (Σ _ : Unit, ProjIdx N ()) →₀ ℕ) :
    Finsupp.weight (blockWeight (ProjIdx N)) d () = ∑ x, d x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«weight_projIdx» := P2M_GroundTheory_Heights__Heights_FieldNumbers_weight_projIdx_e108999e94b3
