-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_X_isHomogeneous_22912e03dba4
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_X_isHomogeneous_22912e03dba4
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:36:51.214263+00:00
-- url     : https://prove2.me/theorems/7338d14e-067b-46c5-a00d-ced46cfa25c9
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of X is Homogeneous 22912e03dba4: P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of X is Homogeneous 22912e03dba4
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of X is Homogeneous 22912e03dba4 construction uses the P2 M Ground Theory Heights  Heights Rest Terms vandermonde Of X is Homogeneous 22912e03dba4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFrobeniusCharacterFormula.lean#L21-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFrobeniusCharacterFormula.lean#L21-L34

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_X_isHomogeneous_22912e03dba4 (r : ℕ) :
    (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ))).IsHomogeneous
      (r * (r - 1) / 2) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«vandermondeOf_X_isHomogeneous» := P2M_GroundTheory_Heights__Heights_RestTerms_vandermondeOf_X_isHomogeneous_22912e03dba4
