-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegralReal_map_68b8ee4ccd2f
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegralReal_map_68b8ee4ccd2f
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:46:18.079834+00:00
-- url     : https://prove2.me/theorems/8271289a-206b-42dc-b01c-a1f592b64b2b
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms flag Integral Real map 68b8ee4ccd2f: P2 M Ground Theory Heights  Heights Rest Terms flag Integral Real map 68b8ee4ccd2f
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms flag Integral Real map 68b8ee4ccd2f construction uses the P2 M Ground Theory Heights  Heights Rest Terms flag Integral Real map 68b8ee4ccd2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/FlagIntegralRealEqMulDdConst.lean#L17-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoeffRenameProdCongrRight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_FlagIntegralRealEqMulDdConst
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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegralReal_map_68b8ee4ccd2f (f N : ℕ) (Φ : RootRing f N) :
    flagIntegralReal f N (map (algebraMap ℚ ℝ) Φ) = (flagIntegral f N Φ : ℝ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«flagIntegralReal_map» := P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegralReal_map_68b8ee4ccd2f
