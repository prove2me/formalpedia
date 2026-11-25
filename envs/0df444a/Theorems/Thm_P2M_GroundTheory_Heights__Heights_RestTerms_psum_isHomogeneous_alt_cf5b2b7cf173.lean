-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_psum_isHomogeneous_alt_cf5b2b7cf173
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_psum_isHomogeneous_alt_cf5b2b7cf173
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:36:09.368386+00:00
-- url     : https://prove2.me/theorems/f3f54d7d-3d95-4378-84ee-6bd755c431c5
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms psum is Homogeneous alt cf5b2b7cf173: P2 M Ground Theory Heights  Heights Rest Terms psum is Homogeneous alt cf5b2b7cf173
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms psum is Homogeneous alt cf5b2b7cf173 construction uses the P2 M Ground Theory Heights  Heights Rest Terms psum is Homogeneous alt cf5b2b7cf173 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchPowerSumHomWeighted.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PSchPowerSumHomWeighted.lean#L10-L11

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsSchur
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PSchPowerSumHomWeighted
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_psum_isHomogeneous_alt_cf5b2b7cf173 (N j : ℕ) : (psum (Fin N) ℚ j).IsHomogeneous j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«psum_isHomogeneous_alt» := P2M_GroundTheory_Heights__Heights_RestTerms_psum_isHomogeneous_alt_cf5b2b7cf173
