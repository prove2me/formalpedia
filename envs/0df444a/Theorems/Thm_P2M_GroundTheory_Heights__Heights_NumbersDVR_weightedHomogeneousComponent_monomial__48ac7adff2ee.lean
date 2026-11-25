-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_monomial__48ac7adff2ee
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_monomial__48ac7adff2ee
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:57.743741+00:00
-- url     : https://prove2.me/theorems/ad51c376-a65f-5e94-8d74-3bc1f2ac332d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component monomial  48ac7adff2ee: P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component monomial  48ac7adf
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component monomial  48ac7adff2ee construction uses the P2 M Ground Theory Heights  Heights Numbers DVR weighted Homogeneous Component monomial  48ac7adff2ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpModel.lean#L22-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PBlowUpModel.lean#L22-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsReesAlgebraDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlowUpModel
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
universe u
variable {σ : Type*} {R : Type*} [CommRing R]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_monomial__48ac7adff2ee {M : Type*} [AddCommMonoid M] [DecidableEq M]
    (w : σ → M) (n : M) (d : σ →₀ ℕ) (c : R) :
    weightedHomogeneousComponent w n (monomial d c) =
      if Finsupp.weight w d = n then monomial d c else 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«weightedHomogeneousComponent_monomial'» := P2M_GroundTheory_Heights__Heights_NumbersDVR_weightedHomogeneousComponent_monomial__48ac7adff2ee
