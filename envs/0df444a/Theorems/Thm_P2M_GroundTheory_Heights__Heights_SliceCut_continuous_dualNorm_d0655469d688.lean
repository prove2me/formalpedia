-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_continuous_dualNorm_d0655469d688
-- name    : P2M_GroundTheory_Heights__Heights_SliceCut_continuous_dualNorm_d0655469d688
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:47:06.905427+00:00
-- url     : https://prove2.me/theorems/62eade37-4116-48f6-b057-b1008cdef9a3
-- title:
--   P2 M Ground Theory Heights  Heights Slice Cut continuous dual Norm d0655469d688: P2 M Ground Theory Heights  Heights Slice Cut continuous dual Norm d0655469d688
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Cut continuous dual Norm d0655469d688 construction uses the P2 M Ground Theory Heights  Heights Slice Cut continuous dual Norm d0655469d688 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L19-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceSectionMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_SliceCut
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
open scoped ContDiff
noncomputable section
open GroundTheory.Heights₂.Heights.SliceCut
variable {n : ℕ} (h : HermNorm n)

theorem P2M_GroundTheory_Heights__Heights_SliceCut_continuous_dualNorm_d0655469d688 : Continuous h.dualNorm := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceCut».«continuous_dualNorm» := P2M_GroundTheory_Heights__Heights_SliceCut_continuous_dualNorm_d0655469d688
