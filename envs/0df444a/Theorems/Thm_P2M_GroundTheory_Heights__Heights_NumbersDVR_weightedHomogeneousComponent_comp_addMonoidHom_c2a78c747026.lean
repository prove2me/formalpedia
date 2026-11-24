-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_comp_addMonoidHom_c2a78c747026
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_comp_addMonoidHom_c2a78c747026
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:59.254224+00:00
-- url     : https://prove2.me/theorems/91349d01-dc5b-4182-aea4-85b717c7b8c2
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component comp add Monoid Hom c2a78c747026: P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component comp add
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component comp add Monoid Hom c2a78c747026 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component comp add Monoid Hom c2a78c747026 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMinimalPrimeMultiHomog.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMinimalPrimeMultiHomog.lean#L17-L23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
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
variable {σ R M M' : Type*} [CommRing R] [AddCommMonoid M] [AddCommMonoid M']

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_comp_addMonoidHom_c2a78c747026 (φ : M →+ M') (hφ : Function.Injective φ)
    (w : σ → M) (b : M) (f : MvPolynomial σ R) :
    weightedHomogeneousComponent (fun v => φ (w v)) (φ b) f = weightedHomogeneousComponent w b f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«weightedHomogeneousComponent_comp_addMonoidHom» := P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_comp_addMonoidHom_c2a78c747026
