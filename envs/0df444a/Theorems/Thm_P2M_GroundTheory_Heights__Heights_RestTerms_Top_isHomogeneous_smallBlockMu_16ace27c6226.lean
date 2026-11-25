-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_smallBlockMu_16ace27c6226
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_smallBlockMu_16ace27c6226
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:21:39.345213+00:00
-- url     : https://prove2.me/theorems/476f9b9d-5676-5c4f-9a22-d0146ce1bff3
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top is Homogeneous small Block Mu 16ace27c6226: P2 M Ground Theory Heights  Heights Rest Terms Top is Homogeneous small Block Mu 16ace27c6226
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top is Homogeneous small Block Mu 16ace27c6226 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top is Homogeneous small Block Mu 16ace27c6226 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L45-L47

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_smallBlockMu_16ace27c6226 (f r a : ℕ) (c : SmallBlock) :
    (smallBlockMu f r a c).IsHomogeneous 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«isHomogeneous_smallBlockMu» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_smallBlockMu_16ace27c6226
