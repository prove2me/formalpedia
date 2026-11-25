-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_prod_fin_add_one_eq_factorial_7ef4a563eab9
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_prod_fin_add_one_eq_factorial_7ef4a563eab9
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:04:30.34377+00:00
-- url     : https://prove2.me/theorems/f5be46c1-c41f-4bde-8312-558f8eca1255
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms prod fin add one eq factorial 7ef4a563eab9: P2 M Ground Theory Heights  Heights Rest Terms prod fin add one eq factorial 7ef4a563eab9
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms prod fin add one eq factorial 7ef4a563eab9 construction uses the P2 M Ground Theory Heights  Heights Rest Terms prod fin add one eq factorial 7ef4a563eab9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PTotalIdentity.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PTotalIdentity.lean#L10-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PTotalIdentity
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
open Finset

theorem P2M_GroundTheory_Heights__Heights_RestTerms_prod_fin_add_one_eq_factorial_7ef4a563eab9 (n : ℕ) :
    ∏ j : Fin n, ((j : ℚ) + 1) = (n.factorial : ℚ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«prod_fin_add_one_eq_factorial» := P2M_GroundTheory_Heights__Heights_RestTerms_prod_fin_add_one_eq_factorial_7ef4a563eab9
