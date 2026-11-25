-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_zero_mem_KSet_rankTwo_9c1fdb6b33be
-- name    : P2M_GroundTheory_Heights__Heights_TheoremB_zero_mem_KSet_rankTwo_9c1fdb6b33be
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T13:40:19.168891+00:00
-- url     : https://prove2.me/theorems/1e1a6dcf-945f-59c0-ad3a-bd1dbcfa1a58
-- title:
--   P2 M Ground Theory Heights  Heights Theorem B zero mem KSet rank Two 9c1fdb6b33be: P2 M Ground Theory Heights  Heights Theorem B zero mem KSet rank Two 9c1fdb6b33be
-- statement:
--   The P2 M Ground Theory Heights  Heights Theorem B zero mem KSet rank Two 9c1fdb6b33be construction uses the P2 M Ground Theory Heights  Heights Theorem B zero mem KSet rank Two 9c1fdb6b33be property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L443-L451
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/MultinomialWeights/Statements.lean#L443-L451

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset
variable (d : IndexData)

theorem P2M_GroundTheory_Heights__Heights_TheoremB_zero_mem_KSet_rankTwo_9c1fdb6b33be : (0 : Weight d1) ∈ KSet d1 0 (quarterInverseN d1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TheoremB».«zero_mem_KSet_rankTwo» := P2M_GroundTheory_Heights__Heights_TheoremB_zero_mem_KSet_rankTwo_9c1fdb6b33be
