-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_of_isMultiHomogIdeal__19cf94e31a60
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_of_isMultiHomogIdeal__19cf94e31a60
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:11:40.163693+00:00
-- url     : https://prove2.me/theorems/6da8e97d-05e6-4d08-b109-f32459f7f1ff
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous of is Multi Homog Ideal  19cf94e31a60: P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous of is Multi Homog Ideal  19cf94e31a
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous of is Multi Homog Ideal  19cf94e31a60 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR is Homogeneous of is Multi Homog Ideal  19cf94e31a60 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSupSpanMultiHomog.lean#L13-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSupSpanMultiHomog.lean#L13-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
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
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open scoped Classical

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_of_isMultiHomogIdeal__19cf94e31a60 {K : Type*} [DecidableEq K] {ι : K → Type*}
    {R : Type*} [CommRing R] {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) :
    I.IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«isHomogeneous_of_isMultiHomogIdeal'» := P2M_GroundTheory_Heights__Heights_NumbersDVR_isHomogeneous_of_isMultiHomogIdeal__19cf94e31a60
