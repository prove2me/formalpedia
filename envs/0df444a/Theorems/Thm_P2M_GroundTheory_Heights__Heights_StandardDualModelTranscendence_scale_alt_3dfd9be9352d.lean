-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_alt_3dfd9be9352d
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_alt_3dfd9be9352d
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:39:29.041801+00:00
-- url     : https://prove2.me/theorems/e2ebf59d-8a96-407c-908a-fc233bccfb45
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale alt 3dfd9be9352d: P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale alt 3dfd9be9352d
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale alt 3dfd9be9352d construction uses the P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale alt 3dfd9be9352d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdModelTransc.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdModelTransc.lean#L85-L87

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

theorem P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_alt_3dfd9be9352d {a : ProjField K i} (ha : a ≠ 0) :
    scale ha (dualStdModelT K i) = dualStdModelEmb K i a⁻¹ * dualStdModelT K i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualModelTranscendence».«scale_alt» := P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_alt_3dfd9be9352d
