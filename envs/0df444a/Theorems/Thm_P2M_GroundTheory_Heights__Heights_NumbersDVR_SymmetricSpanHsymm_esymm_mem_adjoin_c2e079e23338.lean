-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_esymm_mem_adjoin_c2e079e23338
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_esymm_mem_adjoin_c2e079e23338
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:08:44.762535+00:00
-- url     : https://prove2.me/theorems/6d19c35d-c051-4668-8e19-a30589f60426
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm esymm mem adjoin c2e079e23338: P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm esymm mem adjoin c2e079e23338
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm esymm mem adjoin c2e079e23338 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm esymm mem adjoin c2e079e23338 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSymmetricSpanHsymm.lean#L22-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSymmetricSpanHsymm.lean#L22-L39

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_esymm_mem_adjoin_c2e079e23338 (k : ℕ) :
    esymm σ ℤ k ∈ Algebra.adjoin ℤ (Set.range (hsymm σ ℤ)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SymmetricSpanHsymm».«esymm_mem_adjoin» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_esymm_mem_adjoin_c2e079e23338
