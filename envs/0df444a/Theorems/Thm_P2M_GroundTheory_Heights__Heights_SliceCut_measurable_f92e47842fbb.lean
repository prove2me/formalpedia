-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_measurable_f92e47842fbb
-- name    : P2M_GroundTheory_Heights__Heights_SliceCut_measurable_f92e47842fbb
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:04.426416+00:00
-- url     : https://prove2.me/theorems/62650b2c-3f42-4ac1-948c-cefeeb769984
-- title:
--   P2 M Ground Theory Heights  Heights Slice Cut measurable f92e47842fbb: P2 M Ground Theory Heights  Heights Slice Cut measurable f92e47842fbb
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Cut measurable f92e47842fbb construction uses the P2 M Ground Theory Heights  Heights Slice Cut measurable f92e47842fbb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L85-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L85-L86

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

theorem P2M_GroundTheory_Heights__Heights_SliceCut_measurable_f92e47842fbb (k : ℕ) : Measurable (sliceCut h k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceCut».«measurable» := P2M_GroundTheory_Heights__Heights_SliceCut_measurable_f92e47842fbb
