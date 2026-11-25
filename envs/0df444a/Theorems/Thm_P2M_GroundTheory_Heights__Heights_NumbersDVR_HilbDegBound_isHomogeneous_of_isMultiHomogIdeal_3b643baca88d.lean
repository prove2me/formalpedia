-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_isHomogeneous_of_isMultiHomogIdeal_3b643baca88d
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_isHomogeneous_of_isMultiHomogIdeal_3b643baca88d
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:28.869958+00:00
-- url     : https://prove2.me/theorems/0123983e-b858-4b53-8916-1cd929181258
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound is Homogeneous of is Multi Homog Ideal 3b643baca88d: P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound is Homogeneous of is
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound is Homogeneous of is Multi Homog Ideal 3b643baca88d construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Hilb Deg Bound is Homogeneous of is Multi Homog Ideal 3b643baca88d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHilbDegBound.lean#L21-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PHilbDegBound.lean#L21-L37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PHilbDegBound
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
open GroundTheory.Heights₂.Heights.NumbersDVR.HilbDegBound
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_isHomogeneous_of_isMultiHomogIdeal_3b643baca88d {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) :
    I.IsHomogeneous (weightedHomogeneousSubmodule F (blockWeight ι)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«HilbDegBound».«isHomogeneous_of_isMultiHomogIdeal» := P2M_GroundTheory_Heights__Heights_NumbersDVR_HilbDegBound_isHomogeneous_of_isMultiHomogIdeal_3b643baca88d
