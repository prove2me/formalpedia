-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_dvd_of_collapse_eq_zero_1f3904f429e5
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_dvd_of_collapse_eq_zero_1f3904f429e5
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:19:31.57192+00:00
-- url     : https://prove2.me/theorems/8a6ab891-be61-59e3-b22a-4b59cd07432d
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Diff Prime dvd of collapse eq zero 1f3904f429e5: P2 M Ground Theory Heights  Heights Rest Terms Flag Diff Prime dvd of collapse eq zero 1f3904f429e5
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Diff Prime dvd of collapse eq zero 1f3904f429e5 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Diff Prime dvd of collapse eq zero 1f3904f429e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagDiffPrime.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagDiffPrime.lean#L45-L47

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_dvd_of_collapse_eq_zero_1f3904f429e5 (a b : σ) {P : MvPolynomial σ ℚ}
    (h : collapse a b P = 0) : (X a - X b : MvPolynomial σ ℚ) ∣ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagDiffPrime».«dvd_of_collapse_eq_zero» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_dvd_of_collapse_eq_zero_1f3904f429e5
