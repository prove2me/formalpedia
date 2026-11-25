-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_hsymm_int_5d930b32fefa
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_hsymm_int_5d930b32fefa
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:09:20.176885+00:00
-- url     : https://prove2.me/theorems/dd2dd055-3527-4992-9e4f-d54614a4cbdf
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm is Homogeneous hsymm int 5d930b32fefa: P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm is Homogeneous hsymm in
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm is Homogeneous hsymm int 5d930b32fefa construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm is Homogeneous hsymm int 5d930b32fefa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSymmetricSpanHsymm.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSymmetricSpanHsymm.lean#L51-L55

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_hsymm_int_5d930b32fefa (a : ℕ) : (hsymm σ ℤ a).IsHomogeneous a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SymmetricSpanHsymm».«isHomogeneous_hsymm_int» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_hsymm_int_5d930b32fefa
