-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_toN_xSign_d28353530503
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_toN_xSign_d28353530503
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:35:36.55787+00:00
-- url     : https://prove2.me/theorems/fca6d533-ae89-47a2-8fb9-d0637491d871
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top to N x Sign d28353530503: P2 M Ground Theory Heights  Heights Rest Terms Top to N x Sign d28353530503
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top to N x Sign d28353530503 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top to N x Sign d28353530503 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L52-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/BlockValue.lean#L52-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_toN_xSign_d28353530503 (r a : ℕ) (c : SmallBlock) (p : MvPolynomial (Fin (r + a)) ℚ) :
    toN (r + a) (xSign r a c p) = aeval (fun i : Fin (r + a) => C c.sign * X i) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«toN_xSign» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_toN_xSign_d28353530503
