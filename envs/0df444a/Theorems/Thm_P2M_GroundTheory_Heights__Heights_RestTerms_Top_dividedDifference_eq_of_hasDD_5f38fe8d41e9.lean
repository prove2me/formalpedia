-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_dividedDifference_eq_of_hasDD_5f38fe8d41e9
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_dividedDifference_eq_of_hasDD_5f38fe8d41e9
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:43.550387+00:00
-- url     : https://prove2.me/theorems/4b083205-ccff-411a-bcbf-49dbeed25908
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top divided Difference eq of has DD 5f38fe8d41e9: P2 M Ground Theory Heights  Heights Rest Terms Top divided Difference eq of has DD 5f38fe8d41e9
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top divided Difference eq of has DD 5f38fe8d41e9 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top divided Difference eq of has DD 5f38fe8d41e9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/Expand.lean#L40-L44

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_dividedDifference_eq_of_hasDD_5f38fe8d41e9 {f N : ℕ} {H P : RootRing f N} (h : HasDD f N H P) :
    dividedDifference f N H = algebraMap (RootRing f N) (FractionRing (RootRing f N)) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«dividedDifference_eq_of_hasDD» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_dividedDifference_eq_of_hasDD_5f38fe8d41e9
