-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_add_23cf9d873983
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_add_23cf9d873983
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:21:32.741538+00:00
-- url     : https://prove2.me/theorems/abd1cec6-9c83-4cba-a780-7536242285b0
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top has DD add 23cf9d873983: P2 M Ground Theory Heights  Heights Rest Terms Top has DD add 23cf9d873983
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top has DD add 23cf9d873983 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top has DD add 23cf9d873983 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L69-L71

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_add_23cf9d873983 {f N : ℕ} {H H' P P' : RootRing f N} (h : HasDD f N H P) (h' : HasDD f N H' P') :
    HasDD f N (H + H') (P + P') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«hasDD_add» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_hasDD_add_23cf9d873983
