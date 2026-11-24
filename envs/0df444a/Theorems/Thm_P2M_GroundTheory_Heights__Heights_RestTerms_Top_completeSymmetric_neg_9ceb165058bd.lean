-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_completeSymmetric_neg_9ceb165058bd
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_completeSymmetric_neg_9ceb165058bd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:09:08.178806+00:00
-- url     : https://prove2.me/theorems/9f9ef36b-fdab-418f-acfb-b6797992d8b3
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top complete Symmetric neg 9ceb165058bd: P2 M Ground Theory Heights  Heights Rest Terms Top complete Symmetric neg 9ceb165058bd
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top complete Symmetric neg 9ceb165058bd construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top complete Symmetric neg 9ceb165058bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L163-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L163-L165

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
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
open GroundTheory.Heights₂.Heights.RestTerms
open GroundTheory.Heights₂.Heights.RestTerms.Top
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_completeSymmetric_neg_9ceb165058bd (σ : Type*) [Fintype σ] [DecidableEq σ] {d : ℤ} (hd : d < 0) :
    completeSymmetric σ d = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«completeSymmetric_neg» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_completeSymmetric_neg_9ceb165058bd
