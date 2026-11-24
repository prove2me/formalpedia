-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockCoeff_rect_eq_7d9159b82c6d
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockCoeff_rect_eq_7d9159b82c6d
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:14.939798+00:00
-- url     : https://prove2.me/theorems/a6085579-8431-4b3f-a25e-91ec34edf609
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Top block Coeff rect eq 7d9159b82c6d: P2 M Ground Theory Heights  Heights Rest Terms Top block Coeff rect eq 7d9159b82c6d
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Top block Coeff rect eq 7d9159b82c6d construction uses the P2 M Ground Theory Heights  Heights Rest Terms Top block Coeff rect eq 7d9159b82c6d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L84-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSameFactorFormula.lean#L84-L91

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockCoeff_rect_eq_7d9159b82c6d (hCI : CharacterAtIdentity.Statement) (r a : ℕ) (hra : r * a ≠ 0) :
    blockCoeff 0 (r * a) (rectangle r a) = numStandardTable (rectangle r a) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Top».«blockCoeff_rect_eq» := P2M_GroundTheory_Heights__Heights_RestTerms_Top_blockCoeff_rect_eq_7d9159b82c6d
