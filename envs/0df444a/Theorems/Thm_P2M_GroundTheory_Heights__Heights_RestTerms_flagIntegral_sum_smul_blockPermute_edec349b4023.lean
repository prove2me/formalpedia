-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegral_sum_smul_blockPermute_edec349b4023
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegral_sum_smul_blockPermute_edec349b4023
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:36:23.252151+00:00
-- url     : https://prove2.me/theorems/ea42c8be-305b-514b-8a8f-850714de1d22
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms flag Integral sum smul block Permute edec349b4023: P2 M Ground Theory Heights  Heights Rest Terms flag Integral sum smul block Permute edec349b4023
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms flag Integral sum smul block Permute edec349b4023 construction uses the P2 M Ground Theory Heights  Heights Rest Terms flag Integral sum smul block Permute edec349b4023 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagIntegralAntisymmetrize.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagIntegralAntisymmetrize.lean#L13-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagIntegralAntisymmetrize
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
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegral_sum_smul_blockPermute_edec349b4023 (f N : ℕ) (H : RootRing f N)
    (s : Finset (Fin f → Equiv.Perm (Fin N))) :
    flagIntegral f N (∑ w ∈ s, blockSign f N w • blockPermute f N w H) =
      ∑ w ∈ s, blockSign f N w * flagIntegral f N (blockPermute f N w H) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«flagIntegral_sum_smul_blockPermute» := P2M_GroundTheory_Heights__Heights_RestTerms_flagIntegral_sum_smul_blockPermute_edec349b4023
