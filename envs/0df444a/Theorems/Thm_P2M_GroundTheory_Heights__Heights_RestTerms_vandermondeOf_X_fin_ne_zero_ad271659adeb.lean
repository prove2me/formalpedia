-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_X_fin_ne_zero_ad271659adeb
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_X_fin_ne_zero_ad271659adeb
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:52.479693+00:00
-- url     : https://prove2.me/theorems/a117e1f6-ef8e-5e08-b85b-81b378d90c02
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of X fin ne zero ad271659adeb: P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of X fin ne zero ad271659adeb
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of X fin ne zero ad271659adeb construction uses the P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of X fin ne zero ad271659adeb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFrobeniusCharacterFormula.lean#L13-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFrobeniusCharacterFormula.lean#L13-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_AltCoeff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFrobeniusCharacterFormula
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_X_fin_ne_zero_ad271659adeb (r : ℕ) :
    vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«vandermondeOf_X_fin_ne_zero» := P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_X_fin_ne_zero_ad271659adeb
