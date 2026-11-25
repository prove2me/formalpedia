-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_decompose_blockWeight_8e63e41e72c9
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_decompose_blockWeight_8e63e41e72c9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:37.240598+00:00
-- url     : https://prove2.me/theorems/2d5c2a2c-ee62-4901-a687-7c4b3a7ca334
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR decompose block Weight 8e63e41e72c9: P2 M Ground Theory Heights  Heights Numbers DVR decompose block Weight 8e63e41e72c9
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR decompose block Weight 8e63e41e72c9 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR decompose block Weight 8e63e41e72c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPrimeFiltration.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPrimeFiltration.lean#L15-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPrimeFiltration
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
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_decompose_blockWeight_8e63e41e72c9 {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*}
    (r : MRing ι R) (b : K → ℕ) :
    (DirectSum.decompose (weightedHomogeneousSubmodule R (blockWeight ι)) r b : MRing ι R) =
      weightedHomogeneousComponent (blockWeight ι) b r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«decompose_blockWeight» := P2M_GroundTheory_Heights__Heights_NumbersDVR_decompose_blockWeight_8e63e41e72c9
