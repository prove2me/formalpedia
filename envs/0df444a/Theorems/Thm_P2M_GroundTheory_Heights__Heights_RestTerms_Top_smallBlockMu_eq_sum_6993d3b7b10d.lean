-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_smallBlockMu_eq_sum_6993d3b7b10d
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_smallBlockMu_eq_sum_6993d3b7b10d
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:35:36.078421+00:00
-- url     : https://prove2.me/theorems/7ee403d1-ac78-4b20-9aaa-e4e3c5ae9092
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top small Block Mu eq sum 6993d3b7b10d: P2 M Ground Theory Heights  Heights Rest Terms Top small Block Mu eq sum 6993d3b7b10d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top small Block Mu eq sum 6993d3b7b10d construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top small Block Mu eq sum 6993d3b7b10d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L153-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L153-L157

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_smallBlockMu_eq_sum_6993d3b7b10d (f r a : ℕ) (c : SmallBlock) :
    smallBlockMu f r a c = ∑ σ : Fin f, blockEmb f (r + a) σ (yEval r a c (psum (Fin r) ℚ 1)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«smallBlockMu_eq_sum» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_smallBlockMu_eq_sum_6993d3b7b10d
