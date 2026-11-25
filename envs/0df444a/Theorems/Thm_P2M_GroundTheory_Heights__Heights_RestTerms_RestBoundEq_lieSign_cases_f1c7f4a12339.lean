-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_lieSign_cases_f1c7f4a12339
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_lieSign_cases_f1c7f4a12339
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:20:33.557386+00:00
-- url     : https://prove2.me/theorems/252b23e3-3b77-48e1-b14a-6b582149e79b
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq lie Sign cases f1c7f4a12339: P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq lie Sign cases f1c7f4a12339
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq lie Sign cases f1c7f4a12339 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq lie Sign cases f1c7f4a12339 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/DegPolynomialIsHomogeneous.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/DegPolynomialIsHomogeneous.lean#L17-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PRestPolynomialHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PVandermondeOfHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_DegPolynomialIsHomogeneous
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
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq

theorem P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_lieSign_cases_f1c7f4a12339 (bot b : Bool) (m : ℕ) : lieSign bot b m = 1 ∨ lieSign bot b m = -1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«RestBoundEq».«lieSign_cases» := P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_lieSign_cases_f1c7f4a12339
