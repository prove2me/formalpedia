-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_iff_isHomogeneous_ee97d9b388e0
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_iff_isHomogeneous_ee97d9b388e0
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:16:56.326197+00:00
-- url     : https://prove2.me/theorems/46aa9bab-e010-572f-855c-571febdb859e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal iff is Homogeneous ee97d9b388e0: P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal iff is Homogeneous ee97d9b388
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal iff is Homogeneous ee97d9b388e0 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Multi Homog Ideal iff is Homogeneous ee97d9b388e0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPrimeFiltration.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PPrimeFiltration.lean#L21-L30

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

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_iff_isHomogeneous_ee97d9b388e0 {R : Type*} [CommRing R] {K : Type*} [Fintype K] [DecidableEq K]
    {ι : K → Type*} (I : Ideal (MRing ι R)) :
    IsMultiHomogIdeal I ↔ I.IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isMultiHomogIdeal_iff_isHomogeneous» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isMultiHomogIdeal_iff_isHomogeneous_ee97d9b388e0
