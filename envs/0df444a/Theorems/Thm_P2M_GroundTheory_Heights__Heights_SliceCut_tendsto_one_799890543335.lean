-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SliceCut_tendsto_one_799890543335
-- name    : P2M_GroundTheory_Heights__Heights_SliceCut_tendsto_one_799890543335
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:37:29.495969+00:00
-- url     : https://prove2.me/theorems/70e8450a-b5dc-56f2-8c10-b781b313e6a3
-- title:
--   P2 M Ground Theory Heights  Heights Slice Cut tendsto one 799890543335: P2 M Ground Theory Heights  Heights Slice Cut tendsto one 799890543335
-- statement:
--   The P2 M Ground Theory Heights  Heights Slice Cut tendsto one 799890543335 construction uses the P2 M Ground Theory Heights  Heights Slice Cut tendsto one 799890543335 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L77-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/SliceCut.lean#L77-L83

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

theorem P2M_GroundTheory_Heights__Heights_SliceCut_tendsto_one_799890543335 (x : Fin n → ℂ) : Tendsto (fun k => sliceCut h k x) atTop (𝓝 1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SliceCut».«tendsto_one» := P2M_GroundTheory_Heights__Heights_SliceCut_tendsto_one_799890543335
