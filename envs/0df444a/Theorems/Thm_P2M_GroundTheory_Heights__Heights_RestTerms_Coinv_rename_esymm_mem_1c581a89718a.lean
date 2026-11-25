-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_rename_esymm_mem_1c581a89718a
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_rename_esymm_mem_1c581a89718a
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:18:44.596445+00:00
-- url     : https://prove2.me/theorems/e48f4d19-b653-40a3-9b8e-504f8889ffdd
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Coinv rename esymm mem 1c581a89718a: P2 M Ground Theory Heights  Heights Rest Terms Coinv rename esymm mem 1c581a89718a
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Coinv rename esymm mem 1c581a89718a construction uses the P2 M Ground Theory Heights  Heights Rest Terms Coinv rename esymm mem 1c581a89718a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoinvReduction.lean#L29-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/CoinvReduction.lean#L29-L47

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
variable [CharZero K]

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_rename_esymm_mem_1c581a89718a {m : ℕ} (b : Fin f) (h1 : 1 ≤ m) (h2 : m ≤ n) :
    rename (fun i : Fin n => (b, i)) (esymm (Fin n) K m) ∈ psumIdeal K f n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Coinv».«rename_esymm_mem» := P2M_GroundTheory_Heights__Heights_RestTerms_Coinv_rename_esymm_mem_1c581a89718a
