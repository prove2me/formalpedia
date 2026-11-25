-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_isBlockAlternating_antisymmetrize_1230b0a0ab9c
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_isBlockAlternating_antisymmetrize_1230b0a0ab9c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:52.637096+00:00
-- url     : https://prove2.me/theorems/1f9ae9bf-b41c-4fe2-897b-474e1b88ed54
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms is Block Alternating antisymmetrize 1230b0a0ab9c: P2 M Ground Theory Heights  Heights Rest Terms is Block Alternating antisymmetrize 1230b0a0ab9c
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms is Block Alternating antisymmetrize 1230b0a0ab9c construction uses the P2 M Ground Theory Heights  Heights Rest Terms is Block Alternating antisymmetrize 1230b0a0ab9c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/StatementsFlag.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/StatementsFlag.lean#L26-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Inhabitants
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
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
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_isBlockAlternating_antisymmetrize_1230b0a0ab9c (f N : ℕ) (H : RootRing f N) :
    IsBlockAlternating f N (antisymmetrize f N H) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«isBlockAlternating_antisymmetrize» := P2M_GroundTheory_Heights__Heights_RestTerms_isBlockAlternating_antisymmetrize_1230b0a0ab9c
