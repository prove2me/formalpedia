-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_multiset_prod_map_31e7246876ba
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_multiset_prod_map_31e7246876ba
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:10:43.083369+00:00
-- url     : https://prove2.me/theorems/cf2e7f17-d46f-4062-a973-9b3ff42ff4e0
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous multiset prod map 31e7246876ba: P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous multiset prod map 31e7246876ba
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous multiset prod map 31e7246876ba construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous multiset prod map 31e7246876ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependence.lean#L11-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependence.lean#L11-L17

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependence
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
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_multiset_prod_map_31e7246876ba {σ : Type*} (φ : ℕ → MvPolynomial σ ℤ)
    (hφ : ∀ b, (φ b).IsHomogeneous b) (t : Multiset ℕ) : ((t.map φ).prod).IsHomogeneous t.sum := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isHomogeneous_multiset_prod_map» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_multiset_prod_map_31e7246876ba
