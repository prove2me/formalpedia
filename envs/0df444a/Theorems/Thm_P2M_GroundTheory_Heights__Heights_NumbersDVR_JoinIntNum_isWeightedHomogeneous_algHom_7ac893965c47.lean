-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_isWeightedHomogeneous_algHom_7ac893965c47
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_isWeightedHomogeneous_algHom_7ac893965c47
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:34.670824+00:00
-- url     : https://prove2.me/theorems/439d0db6-42f2-400a-884b-d9467b69fefe
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num is Weighted Homogeneous alg Hom 7ac893965c47: P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num is Weighted Homogeneous alg Hom
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num is Weighted Homogeneous alg Hom 7ac893965c47 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Join Int Num is Weighted Homogeneous alg Hom 7ac893965c47 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PJoinIntNum.lean#L15-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsJoinIntNum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PJoinIntNum
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
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (ptIdx liftVar pullDeg)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinIntNum
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_isWeightedHomogeneous_algHom_7ac893965c47 {R : Type*} [CommRing R] {σ τ M N : Type*}
    [AddCommMonoid M] [AddCommMonoid N] (w : σ → M) (w' : τ → N) (L : M →+ N)
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (hφ : ∀ s, IsWeightedHomogeneous w' (φ (X s)) (L (w s)))
    {f : MvPolynomial σ R} {m : M} (hf : IsWeightedHomogeneous w f m) :
    IsWeightedHomogeneous w' (φ f) (L m) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«JoinIntNum».«isWeightedHomogeneous_algHom» := P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinIntNum_isWeightedHomogeneous_algHom_7ac893965c47
