-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_realForm_conjTranspose_41c2e7eb6733
-- name    : P2M_GroundTheory_Heights__Heights_realForm_conjTranspose_41c2e7eb6733
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:50:29.10927+00:00
-- url     : https://prove2.me/theorems/b9fc4f14-87dc-59c8-b6e8-831665f572a9
-- title:
--   P2 M Ground Theory Heights  Heights real Form conj Transpose 41c2e7eb6733: P2 M Ground Theory Heights  Heights real Form conj Transpose 41c2e7eb6733
-- statement:
--   The P2 M Ground Theory Heights  Heights real Form conj Transpose 41c2e7eb6733 construction uses the P2 M Ground Theory Heights  Heights real Form conj Transpose 41c2e7eb6733 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PComplexJacobian.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PComplexJacobian.lean#L31-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PComplexJacobian
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
open Matrix
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_realForm_conjTranspose_41c2e7eb6733 {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℂ) :
    realForm Aᴴ = (realForm A)ᵀ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«realForm_conjTranspose» := P2M_GroundTheory_Heights__Heights_realForm_conjTranspose_41c2e7eb6733
