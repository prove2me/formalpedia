-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_omitProduct_eq_zero_d1cd08c82e98
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_omitProduct_eq_zero_d1cd08c82e98
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T04:20:43.701869+00:00
-- url     : https://prove2.me/theorems/c739edf7-cebe-5aa5-a71a-b5a673fc214f
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Schur coeff omit Product eq zero d1cd08c82e98: P2 M Ground Theory Heights  Heights Rest Terms Schur coeff omit Product eq zero d1cd08c82e98
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Schur coeff omit Product eq zero d1cd08c82e98 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Schur coeff omit Product eq zero d1cd08c82e98 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L100-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/JacobiTrudi.lean#L100-L105

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_omitProduct_eq_zero_d1cd08c82e98 (j : σ) (c : ℕ) (hc : Fintype.card σ ≤ c) :
    PowerSeries.coeff c (omitProduct j) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«Schur».«coeff_omitProduct_eq_zero» := P2M_GroundTheory_Heights__Heights_RestTerms_Schur_coeff_omitProduct_eq_zero_d1cd08c82e98
