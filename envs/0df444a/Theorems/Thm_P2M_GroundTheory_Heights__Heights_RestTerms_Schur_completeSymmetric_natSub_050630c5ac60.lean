-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_completeSymmetric_natSub_050630c5ac60
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Schur_completeSymmetric_natSub_050630c5ac60
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:35.985594+00:00
-- url     : https://prove2.me/theorems/f9716832-6a15-4c4b-a4c7-a312e5122107
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur complete Symmetric nat Sub 050630c5ac60: P2 M Ground Theory Heights  Heights Rest Terms Schur complete Symmetric nat Sub 050630c5ac60
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur complete Symmetric nat Sub 050630c5ac60 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur complete Symmetric nat Sub 050630c5ac60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L157-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L157-L164

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
variable {m : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Schur_completeSymmetric_natSub_050630c5ac60 (σ : Type*) [Fintype σ] [DecidableEq σ] (a c : ℕ) :
    completeSymmetric σ ((a : ℤ) - (c : ℤ)) = if c ≤ a then hsymm σ ℚ (a - c) else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Schur».«completeSymmetric_natSub» := P2M_GroundTheory_Heights__Heights_RestTerms_Schur_completeSymmetric_natSub_050630c5ac60
