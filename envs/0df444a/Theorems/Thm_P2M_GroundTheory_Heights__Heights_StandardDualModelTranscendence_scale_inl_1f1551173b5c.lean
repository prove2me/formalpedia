-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_inl_1f1551173b5c
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_inl_1f1551173b5c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:40:14.144261+00:00
-- url     : https://prove2.me/theorems/46a79ca1-49d8-4fc8-bf2b-4292ca0c5e36
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale inl 1f1551173b5c: P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale inl 1f1551173b5c
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale inl 1f1551173b5c construction uses the P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale inl 1f1551173b5c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdModelTransc.lean#L91-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdModelTransc.lean#L91-L95

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
variable [NumberField K] {F : HermLattice K i} {T : Type} (b : Module.Basis T ℤ (dualLattice F))

theorem P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_inl_1f1551173b5c {a : ProjField K i} (ha : a ≠ 0) (t : T) :
    scale ha (dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)) =
      dualStdModelEmb K i a * dualStdModelPt b (⟨Sum.inl (), t⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualModelTranscendence».«scale_inl» := P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_inl_1f1551173b5c
