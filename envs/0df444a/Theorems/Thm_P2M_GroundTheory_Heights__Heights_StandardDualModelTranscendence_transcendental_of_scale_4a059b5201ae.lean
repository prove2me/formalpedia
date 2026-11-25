-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_transcendental_of_scale_4a059b5201ae
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_transcendental_of_scale_4a059b5201ae
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:39:22.504316+00:00
-- url     : https://prove2.me/theorems/58001728-dc30-4ba2-8fc3-a8d5b3c5e274
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence transcendental of scale 4a059b5201ae: P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence transcendental of scal
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence transcendental of scale 4a059b5201ae construction uses the P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence transcendental of scale 4a059b5201ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdModelTransc.lean#L55-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdModelTransc.lean#L55-L73

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

theorem P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_transcendental_of_scale_4a059b5201ae {R Ω : Type} [CommRing R] [Field Ω] [CharZero Ω] [Algebra R Ω]
    (A : Subalgebra R Ω) {z : Ω} (hz : z ≠ 0)
    (h : ∀ n : ℕ, ∃ σ : Ω →+* Ω, (∀ y ∈ A, σ y = y) ∧ σ z = ((n : Ω) + 1) * z) : Transcendental A z := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualModelTranscendence».«transcendental_of_scale» := P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_transcendental_of_scale_4a059b5201ae
