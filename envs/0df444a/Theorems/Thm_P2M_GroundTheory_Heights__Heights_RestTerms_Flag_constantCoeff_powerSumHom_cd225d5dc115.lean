-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_constantCoeff_powerSumHom_cd225d5dc115
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Flag_constantCoeff_powerSumHom_cd225d5dc115
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:50.063685+00:00
-- url     : https://prove2.me/theorems/9cf4a64a-2430-571c-84ba-f4d673354e7a
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag constant Coeff power Sum Hom cd225d5dc115: P2 M Ground Theory Heights  Heights Rest Terms Flag constant Coeff power Sum Hom cd225d5dc115
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag constant Coeff power Sum Hom cd225d5dc115 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag constant Coeff power Sum Hom cd225d5dc115 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PowerSums.lean#L115-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PowerSums.lean#L115-L122

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Flag_constantCoeff_powerSumHom_cd225d5dc115 (N : ℕ) (S : MvPolynomial (Fin N) ℚ) :
    constantCoeff (powerSumHom N S) = constantCoeff S := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Flag».«constantCoeff_powerSumHom» := P2M_GroundTheory_Heights__Heights_RestTerms_Flag_constantCoeff_powerSumHom_cd225d5dc115
