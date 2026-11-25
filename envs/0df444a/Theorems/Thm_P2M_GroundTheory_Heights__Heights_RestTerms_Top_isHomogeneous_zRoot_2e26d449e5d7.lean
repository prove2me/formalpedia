-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_zRoot_2e26d449e5d7
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_zRoot_2e26d449e5d7
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:21:43.62887+00:00
-- url     : https://prove2.me/theorems/a2ef8506-7b3a-44ec-b43e-92f5a1fe3c23
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top is Homogeneous z Root 2e26d449e5d7: P2 M Ground Theory Heights  Heights Rest Terms Top is Homogeneous z Root 2e26d449e5d7
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top is Homogeneous z Root 2e26d449e5d7 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top is Homogeneous z Root 2e26d449e5d7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L41-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L41-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_BlockValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsCoinv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsTop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSameFactorFormula
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_zRoot_2e26d449e5d7 (f r a : ℕ) (c : SmallBlock) (τ : Fin f) (i : Fin a) :
    (zRoot f r a c τ i).IsHomogeneous 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«isHomogeneous_zRoot» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_zRoot_2e26d449e5d7
