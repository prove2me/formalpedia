-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_powerSumHom_isSymmetric_d4be3b011480
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_powerSumHom_isSymmetric_d4be3b011480
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:55.909379+00:00
-- url     : https://prove2.me/theorems/9c12c3df-7bcf-4de2-b2cf-fe0f9d514fe7
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag power Sum Hom is Symmetric d4be3b011480: P2 M Ground Theory Heights  Heights Rest Terms Flag power Sum Hom is Symmetric d4be3b011480
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag power Sum Hom is Symmetric d4be3b011480 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag power Sum Hom is Symmetric d4be3b011480 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PowerSums.lean#L80-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PowerSums.lean#L80-L93

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PowerSums
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
open GroundTheory.Heights₂.Heights.RestTerms.Flag
open MvPolynomial Finset
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_powerSumHom_isSymmetric_d4be3b011480 (N : ℕ) (S : MvPolynomial (Fin N) ℚ) :
    (powerSumHom N S).IsSymmetric := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«powerSumHom_isSymmetric» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_powerSumHom_isSymmetric_d4be3b011480
