-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_PointIdealMultiProj_coneMap_monomial_isWeightedHomogeneous_3f0ae37a1420
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_PointIdealMultiProj_coneMap_monomial_isWeightedHomogeneous_3f0ae37a1420
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:08:04.390713+00:00
-- url     : https://prove2.me/theorems/40da64a7-512c-4a96-ae4b-ed9bbed77e89
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Point Ideal Multi Proj cone Map monomial is Weighted Homogeneous 3f0ae37a1420: P2 M Ground Theory Heights  Heights Numbers DVR Point Ideal Multi Proj co
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Point Ideal Multi Proj cone Map monomial is Weighted Homogeneous 3f0ae37a1420 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Point Ideal Multi Proj cone Map monomial is Weighted Homogeneous 3f0ae37a1420 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPointIdealMultiProj.lean#L18-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPointIdealMultiProj.lean#L18-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPointIdealMultiProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPointIdealMultiProj
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
open GroundTheory.Heights₂.Heights.NumbersDVR.PointIdealMultiProj
variable {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L]
  {K : Type*} [DecidableEq K] {ι : K → Type*}

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_PointIdealMultiProj_coneMap_monomial_isWeightedHomogeneous_3f0ae37a1420 (z : (Σ k, ι k) → L) (d : (Σ k, ι k) →₀ ℕ) (a : F) :
    IsWeightedHomogeneous (coneWeight K) (pointConeMap F z (monomial d a))
      (Finsupp.weight (blockWeight ι) d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«PointIdealMultiProj».«coneMap_monomial_isWeightedHomogeneous» := P2M_GroundTheory_Heights__Heights_NumbersDVR_PointIdealMultiProj_coneMap_monomial_isWeightedHomogeneous_3f0ae37a1420
