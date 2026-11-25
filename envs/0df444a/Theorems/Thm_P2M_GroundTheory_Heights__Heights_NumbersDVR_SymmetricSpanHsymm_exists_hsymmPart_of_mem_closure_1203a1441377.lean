-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_exists_hsymmPart_of_mem_closure_1203a1441377
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_exists_hsymmPart_of_mem_closure_1203a1441377
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:10:24.81667+00:00
-- url     : https://prove2.me/theorems/22babb4e-39f4-4c72-ae23-1afb2dec4733
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm exists hsymm Part of mem closure 1203a1441377: P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm exists hsymm Pa
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm exists hsymm Part of mem closure 1203a1441377 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm exists hsymm Part of mem closure 1203a1441377 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSymmetricSpanHsymm.lean#L69-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSymmetricSpanHsymm.lean#L69-L84

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_exists_hsymmPart_of_mem_closure_1203a1441377 {x : MvPolynomial σ ℤ}
    (hx : x ∈ Submonoid.closure (Set.range (hsymm σ ℤ))) :
    ∃ (n : ℕ) (μ : n.Partition), x = hsymmPart σ ℤ μ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SymmetricSpanHsymm».«exists_hsymmPart_of_mem_closure» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_exists_hsymmPart_of_mem_closure_1203a1441377
