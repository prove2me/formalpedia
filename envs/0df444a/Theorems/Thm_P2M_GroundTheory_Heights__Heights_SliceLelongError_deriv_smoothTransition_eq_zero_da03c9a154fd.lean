-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceLelongError_deriv_smoothTransition_eq_zero_da03c9a154fd
-- name    : P2M_GroundTheory_Heights__Heights_SliceLelongError_deriv_smoothTransition_eq_zero_da03c9a154fd
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:14:28.986838+00:00
-- url     : https://prove2.me/theorems/bb76854b-ab2c-4cd7-b690-3f29855caea3
-- title:
--   P2 M Ground Theory Heights  Heights Slice Lelong Error deriv smooth Transition eq zero da03c9a154fd: P2 M Ground Theory Heights  Heights Slice Lelong Error deriv smooth Transition eq zero da03c9a154fd
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Lelong Error deriv smooth Transition eq zero da03c9a154fd construction uses the P2 M Ground Theory Heights  Heights Slice Lelong Error deriv smooth Transition eq zero da03c9a154fd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLelongError.lean#L16-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PSliceLelongError.lean#L16-L30

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

theorem P2M_GroundTheory_Heights__Heights_SliceLelongError_deriv_smoothTransition_eq_zero_da03c9a154fd {s : ℝ} (hs : s < 0 ∨ 1 < s) :
    deriv Real.smoothTransition s = 0 ∧ deriv (deriv Real.smoothTransition) s = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceLelongError».«deriv_smoothTransition_eq_zero» := P2M_GroundTheory_Heights__Heights_SliceLelongError_deriv_smoothTransition_eq_zero_da03c9a154fd
