-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_constantCoeff_blockPowerSum_cf00e626cb01
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_constantCoeff_blockPowerSum_cf00e626cb01
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:35:43.743683+00:00
-- url     : https://prove2.me/theorems/e4c01ff4-da54-4daf-a018-e82e56af1f7c
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms constant Coeff block Power Sum cf00e626cb01: P2 M Ground Theory Heights  Heights Rest Terms constant Coeff block Power Sum cf00e626cb01
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms constant Coeff block Power Sum cf00e626cb01 construction uses the P2 M Ground Theory Heights  Heights Rest Terms constant Coeff block Power Sum cf00e626cb01 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagIntegralKillsPowerSums.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagIntegralKillsPowerSums.lean#L12-L14

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagIntegralKillsPowerSums
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
open MvPolynomial Finset

theorem P2M_GroundTheory_Heights__Heights_RestTerms_constantCoeff_blockPowerSum_cf00e626cb01 (f N k : ℕ) (τ : Fin f) (hk : 1 ≤ k) :
    constantCoeff (blockPowerSum f N k τ) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«constantCoeff_blockPowerSum» := P2M_GroundTheory_Heights__Heights_RestTerms_constantCoeff_blockPowerSum_cf00e626cb01
