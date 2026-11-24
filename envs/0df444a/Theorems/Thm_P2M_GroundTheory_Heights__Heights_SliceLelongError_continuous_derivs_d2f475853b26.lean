-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLelongError_continuous_derivs_d2f475853b26
-- name    : P2M_GroundTheory_Heights__Heights_SliceLelongError_continuous_derivs_d2f475853b26
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:15:44.670802+00:00
-- url     : https://prove2.me/theorems/2ac045b2-f4f8-4e9c-bf79-3d1ba39ec4ca
-- title:
--   P2 M Ground Theory Heights  Heights Slice Lelong Error continuous derivs d2f475853b26: P2 M Ground Theory Heights  Heights Slice Lelong Error continuous derivs d2f475853b26
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Lelong Error continuous derivs d2f475853b26 construction uses the P2 M Ground Theory Heights  Heights Slice Lelong Error continuous derivs d2f475853b26 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLelongError.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLelongError.lean#L32-L35

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLelongError
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceWeightBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBandEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLelongError
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.SliceLelongError

theorem P2M_GroundTheory_Heights__Heights_SliceLelongError_continuous_derivs_d2f475853b26 :
    Continuous (deriv Real.smoothTransition) ∧ Continuous (deriv (deriv Real.smoothTransition)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceLelongError».«continuous_derivs» := P2M_GroundTheory_Heights__Heights_SliceLelongError_continuous_derivs_d2f475853b26
