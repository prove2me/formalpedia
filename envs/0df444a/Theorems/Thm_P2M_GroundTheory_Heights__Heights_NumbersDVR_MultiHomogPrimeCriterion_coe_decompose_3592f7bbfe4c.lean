-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_coe_decompose_3592f7bbfe4c
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_coe_decompose_3592f7bbfe4c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:35:01.203076+00:00
-- url     : https://prove2.me/theorems/5bf05fcc-c5ee-4c3d-94bf-96068a28842e
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion coe decompose 3592f7bbfe4c: P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion coe decompose 3592f7
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion coe decompose 3592f7bbfe4c construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Multi Homog Prime Criterion coe decompose 3592f7bbfe4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultiHomogPrimeCriterion.lean#L63-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PMultiHomogPrimeCriterion.lean#L63-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMultiHomogPrimeCriterion
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
open GroundTheory.Heights₂.Heights.NumbersDVR.MultiHomogPrimeCriterion
variable {K : Type} [Fintype K] [DecidableEq K]
variable {ι : K → Type} {R : Type u} [CommRing R]
omit [Fintype K] [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_coe_decompose_3592f7bbfe4c {σ M : Type*} [AddCommMonoid M] {_ : DecidableEq M} (w : σ → M)
    [GradedRing (weightedHomogeneousSubmodule R w)] (r : MvPolynomial σ R) (i : M) :
    (DirectSum.decompose (weightedHomogeneousSubmodule R w) r i : MvPolynomial σ R) =
      weightedHomogeneousComponent w i r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«MultiHomogPrimeCriterion».«coe_decompose» := P2M_GroundTheory_Heights__Heights_NumbersDVR_MultiHomogPrimeCriterion_coe_decompose_3592f7bbfe4c
