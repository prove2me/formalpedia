-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_dvd_sub_collapse_fbe7a1eb7559
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_dvd_sub_collapse_fbe7a1eb7559
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:36.875512+00:00
-- url     : https://prove2.me/theorems/32fb308d-6f4e-5ffe-8b93-3c281474afab
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Diff Prime dvd sub collapse fbe7a1eb7559: P2 M Ground Theory Heights  Heights Rest Terms Flag Diff Prime dvd sub collapse fbe7a1eb7559
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Diff Prime dvd sub collapse fbe7a1eb7559 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Diff Prime dvd sub collapse fbe7a1eb7559 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagDiffPrime.lean#L23-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagDiffPrime.lean#L23-L38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagDiffPrime
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.FlagDiffPrime
variable {σ : Type} [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_dvd_sub_collapse_fbe7a1eb7559 (a b : σ) (Q : MvPolynomial σ ℚ) :
    (X a - X b : MvPolynomial σ ℚ) ∣ Q - collapse a b Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagDiffPrime».«dvd_sub_collapse» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_dvd_sub_collapse_fbe7a1eb7559
