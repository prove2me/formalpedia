-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_prod_map_hsymm_55f0349fa572
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_prod_map_hsymm_55f0349fa572
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:08:35.392394+00:00
-- url     : https://prove2.me/theorems/2d578f75-3c2f-46ef-bf4b-75b76342e1a7
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm is Homogeneous prod map hsymm 55f0349fa572: P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm is Homogeneous pro
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm is Homogeneous prod map hsymm 55f0349fa572 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Symmetric Span Hsymm is Homogeneous prod map hsymm 55f0349fa572 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSymmetricSpanHsymm.lean#L57-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSymmetricSpanHsymm.lean#L57-L63

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_prod_map_hsymm_55f0349fa572 (t : Multiset ℕ) :
    ((t.map (hsymm σ ℤ)).prod).IsHomogeneous t.sum := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«SymmetricSpanHsymm».«isHomogeneous_prod_map_hsymm» := P2M_GroundTheory_Heights__Heights_NumbersDVR_SymmetricSpanHsymm_isHomogeneous_prod_map_hsymm_55f0349fa572
