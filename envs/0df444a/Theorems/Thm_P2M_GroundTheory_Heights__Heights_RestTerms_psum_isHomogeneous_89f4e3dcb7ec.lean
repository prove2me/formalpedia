-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_psum_isHomogeneous_89f4e3dcb7ec
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_psum_isHomogeneous_89f4e3dcb7ec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T04:36:19.702433+00:00
-- url     : https://prove2.me/theorems/74896cec-5e7c-4798-a9d0-aa12891f8acf
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms psum is Homogeneous 89f4e3dcb7ec: P2 M Ground Theory Heights  Heights Rest Terms psum is Homogeneous 89f4e3dcb7ec
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms psum is Homogeneous 89f4e3dcb7ec construction uses the P2 M Ground Theory Heights  Heights Rest Terms psum is Homogeneous 89f4e3dcb7ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFrobeniusCharacterFormula.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFrobeniusCharacterFormula.lean#L36-L39

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_psum_isHomogeneous_89f4e3dcb7ec (σ : Type*) [Fintype σ] (q : ℕ) :
    (psum σ ℚ q).IsHomogeneous q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«psum_isHomogeneous» := P2M_GroundTheory_Heights__Heights_RestTerms_psum_isHomogeneous_89f4e3dcb7ec
