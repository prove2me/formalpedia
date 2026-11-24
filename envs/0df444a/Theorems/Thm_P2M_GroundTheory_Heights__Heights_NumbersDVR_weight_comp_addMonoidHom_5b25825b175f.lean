-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_comp_addMonoidHom_5b25825b175f
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_comp_addMonoidHom_5b25825b175f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:22:05.678632+00:00
-- url     : https://prove2.me/theorems/a0604e02-b9b3-46ea-b722-fe2a24ee52de
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR weight comp add Monoid Hom 5b25825b175f: P2 M Ground Theory Heights  Heights Numbers DVR weight comp add Monoid Hom 5b25825b175f
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR weight comp add Monoid Hom 5b25825b175f construction uses the P2 M Ground Theory Heights  Heights Numbers DVR weight comp add Monoid Hom 5b25825b175f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMinimalPrimeMultiHomog.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMinimalPrimeMultiHomog.lean#L13-L15

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_comp_addMonoidHom_5b25825b175f (φ : M →+ M') (w : σ → M) (d : σ →₀ ℕ) :
    Finsupp.weight (fun v => φ (w v)) d = φ (Finsupp.weight w d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«weight_comp_addMonoidHom» := P2M_GroundTheory_Heights__Heights_NumbersDVR_weight_comp_addMonoidHom_5b25825b175f
