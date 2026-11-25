-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_sum_esymm_mul_hsymm_int_db3c4f679e82
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_sum_esymm_mul_hsymm_int_db3c4f679e82
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:16:50.221853+00:00
-- url     : https://prove2.me/theorems/44586791-598d-5ccf-828d-53c168bf5e24
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm sum esymm mul hsymm int db3c4f679e82: P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm sum esymm mul hsymm int
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm sum esymm mul hsymm int db3c4f679e82 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm sum esymm mul hsymm int db3c4f679e82 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSymmetricSpanHsymm.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSymmetricSpanHsymm.lean#L14-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_Capelli_CompleteHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSymmetricSpanHsymm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial Finset
open GroundTheory.Heights₂.Heights.NumbersDVR.SymmetricSpanHsymm
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_sum_esymm_mul_hsymm_int_db3c4f679e82 {k : ℕ} (hk : k ≠ 0) :
    ∑ s ∈ range (k + 1), (-1) ^ s * esymm σ ℤ s * hsymm σ ℤ (k - s) = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SymmetricSpanHsymm».«sum_esymm_mul_hsymm_int» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_sum_esymm_mul_hsymm_int_db3c4f679e82
