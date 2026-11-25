-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_collapse_eq_zero_of_dvd_cecf2aecafc7
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_collapse_eq_zero_of_dvd_cecf2aecafc7
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:20:03.231132+00:00
-- url     : https://prove2.me/theorems/4002eba0-941b-4a12-aa60-7efb7453b71d
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Flag Diff Prime collapse eq zero of dvd cecf2aecafc7: P2 M Ground Theory Heights  Heights Rest Terms Flag Diff Prime collapse eq zero of dvd cecf2aecafc7
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Flag Diff Prime collapse eq zero of dvd cecf2aecafc7 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Flag Diff Prime collapse eq zero of dvd cecf2aecafc7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagDiffPrime.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/PFlagDiffPrime.lean#L40-L43

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

theorem P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_collapse_eq_zero_of_dvd_cecf2aecafc7 (a b : σ) {P : MvPolynomial σ ℚ}
    (h : (X a - X b : MvPolynomial σ ℚ) ∣ P) : collapse a b P = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«FlagDiffPrime».«collapse_eq_zero_of_dvd» := P2M_GroundTheory_Heights__Heights_RestTerms_FlagDiffPrime_collapse_eq_zero_of_dvd_cecf2aecafc7
