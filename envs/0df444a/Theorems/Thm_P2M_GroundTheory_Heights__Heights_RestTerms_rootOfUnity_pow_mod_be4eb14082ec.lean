-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rootOfUnity_pow_mod_be4eb14082ec
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_rootOfUnity_pow_mod_be4eb14082ec
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T04:36:02.711959+00:00
-- url     : https://prove2.me/theorems/8d0d2516-e1ee-55dd-a730-dd187ae98dd3
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms root Of Unity pow mod be4eb14082ec: P2 M Ground Theory Heights  Heights Rest Terms root Of Unity pow mod be4eb14082ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms root Of Unity pow mod be4eb14082ec construction uses the P2 M Ground Theory Heights  Heights Rest Terms root Of Unity pow mod be4eb14082ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchRootOfUnityRowsEq.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchRootOfUnityRowsEq.lean#L13-L16

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchRootOfUnityRowsEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Complex

theorem P2M_GroundTheory_Heights__Heights_RestTerms_rootOfUnity_pow_mod_be4eb14082ec (k : ℕ) (hk : k ≠ 0) (a : ℕ) :
    rootOfUnity k ^ a = rootOfUnity k ^ (a % k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«rootOfUnity_pow_mod» := P2M_GroundTheory_Heights__Heights_RestTerms_rootOfUnity_pow_mod_be4eb14082ec
