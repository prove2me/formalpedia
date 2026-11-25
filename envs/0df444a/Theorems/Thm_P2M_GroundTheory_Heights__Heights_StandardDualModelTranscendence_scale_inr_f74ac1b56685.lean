-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_inr_f74ac1b56685
-- name    : P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_inr_f74ac1b56685
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:40:58.272809+00:00
-- url     : https://prove2.me/theorems/349caf45-cb2c-4715-9764-627a0200f1c5
-- title:
--   P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale inr f74ac1b56685: P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale inr f74ac1b56685
-- statement:
--   The P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale inr f74ac1b56685 construction uses the P2 M Ground Theory Heights  Heights Standard Dual Model Transcendence scale inr f74ac1b56685 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdModelTransc.lean#L97-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PDualStdModelTransc.lean#L97-L105

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

theorem P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_inr_f74ac1b56685 {a : ProjField K i} (ha : a ≠ 0) (j : PBlk i ()) :
    scale ha (dualStdModelPt b (⟨Sum.inr (), j⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k)) =
      dualStdModelPt b (⟨Sum.inr (), j⟩ : Σ k, Sum.elim (dualBlocks T) (PBlk i) k) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«StandardDualModelTranscendence».«scale_inr» := P2M_GroundTheory_Heights__Heights_StandardDualModelTranscendence_scale_inr_f74ac1b56685
