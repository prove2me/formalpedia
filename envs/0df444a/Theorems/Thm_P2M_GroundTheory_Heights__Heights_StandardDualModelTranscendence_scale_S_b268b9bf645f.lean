-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_S_b268b9bf645f
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_S_b268b9bf645f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:34:57.043333+00:00
-- url     : https://prove2.me/theorems/aa6a10a7-c0de-45cf-af85-2bf2f9028791
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale S b268b9bf645f: P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale S b268b9bf645f
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale S b268b9bf645f construction uses the P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale S b268b9bf645f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdModelTransc.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdModelTransc.lean#L81-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_DualStdModelField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualArithVar
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PDualStdModelTransc
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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.StandardDualModelTranscendence
variable {L : Type} [Field L]
variable {K : Type} [Field K] {i : ℕ}

theorem P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_S_b268b9bf645f {a : ProjField K i} (ha : a ≠ 0) :
    scale ha (dualStdModelS K i) = dualStdModelEmb K i a * dualStdModelS K i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualModelTranscendence».«scale_S» := P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_S_b268b9bf645f
