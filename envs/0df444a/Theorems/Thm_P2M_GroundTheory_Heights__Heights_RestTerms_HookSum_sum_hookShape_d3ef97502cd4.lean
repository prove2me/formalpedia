-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_sum_hookShape_d3ef97502cd4
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_sum_hookShape_d3ef97502cd4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:45:13.13387+00:00
-- url     : https://prove2.me/theorems/ad7e5965-e2e7-4457-9b6a-12f4e6255a4c
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Hook Sum sum hook Shape d3ef97502cd4: P2 M Ground Theory Heights  Heights Rest Terms Hook Sum sum hook Shape d3ef97502cd4
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Hook Sum sum hook Shape d3ef97502cd4 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Hook Sum sum hook Shape d3ef97502cd4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookCharacterSumIdentity.lean#L41-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PHookCharacterSumIdentity.lean#L41-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Expand
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PHookCharacterSumIdentity
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
open GroundTheory.Heights₂.Heights.RestTerms.HookSum

theorem P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_sum_hookShape_d3ef97502cd4 (r k l : ℕ) (hl : l < r) : ∑ i, hookShape r k l i = (k - l) + l := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«HookSum».«sum_hookShape» := P2M_GroundTheory_Heights__Heights_RestTerms_HookSum_sum_hookShape_d3ef97502cd4
