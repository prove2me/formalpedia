-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_bps_mem_psumIdeal_6a4fee1897e0
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_bps_mem_psumIdeal_6a4fee1897e0
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:44.207811+00:00
-- url     : https://prove2.me/theorems/b6e1127f-ce8e-4556-8122-2210ca400ea1
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Coinv bps mem psum Ideal 6a4fee1897e0: P2 M Ground Theory Heights  Heights Rest Terms Coinv bps mem psum Ideal 6a4fee1897e0
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Coinv bps mem psum Ideal 6a4fee1897e0 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Coinv bps mem psum Ideal 6a4fee1897e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoinvReduction.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoinvReduction.lean#L19-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_CoinvReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Coinv
open MvPolynomial Finset
noncomputable section
variable (K : Type*) [Field K] (f n : ℕ)
variable {K f n}

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_bps_mem_psumIdeal_6a4fee1897e0 {m : ℕ} (b : Fin f) (h1 : 1 ≤ m) (h2 : m ≤ n) :
    bps K f n m b ∈ psumIdeal K f n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Coinv».«bps_mem_psumIdeal» := P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_bps_mem_psumIdeal_6a4fee1897e0
