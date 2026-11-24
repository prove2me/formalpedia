-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_yRoot_d0d8d9eadb63
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_yRoot_d0d8d9eadb63
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:10:57.554297+00:00
-- url     : https://prove2.me/theorems/6009a2d6-ce64-41e6-bb52-b4a7243302b4
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top is Homogeneous y Root d0d8d9eadb63: P2 M Ground Theory Heights  Heights Rest Terms Top is Homogeneous y Root d0d8d9eadb63
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top is Homogeneous y Root d0d8d9eadb63 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top is Homogeneous y Root d0d8d9eadb63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L36-L39

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_yRoot_d0d8d9eadb63 (f r a : ℕ) (c : SmallBlock) (τ : Fin f) (i : Fin r) :
    (yRoot f r a c τ i).IsHomogeneous 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«isHomogeneous_yRoot» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_isHomogeneous_yRoot_d0d8d9eadb63
