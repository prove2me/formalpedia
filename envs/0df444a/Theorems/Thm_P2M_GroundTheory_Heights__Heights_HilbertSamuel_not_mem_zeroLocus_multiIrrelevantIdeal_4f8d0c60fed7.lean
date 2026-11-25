-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_not_mem_zeroLocus_multiIrrelevantIdeal_4f8d0c60fed7
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_not_mem_zeroLocus_multiIrrelevantIdeal_4f8d0c60fed7
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:25:00.073442+00:00
-- url     : https://prove2.me/theorems/ccaf90a4-b9b4-53a2-9aeb-5b4049472b37
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel not mem zero Locus multi Irrelevant Ideal 4f8d0c60fed7: P2 M Ground Theory Heights  Heights Hilbert Samuel not mem zero Locus multi Irrelevant Ideal
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel not mem zero Locus multi Irrelevant Ideal 4f8d0c60fed7 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel not mem zero Locus multi Irrelevant Ideal 4f8d0c60fed7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PClopenComponents.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PClopenComponents.lean#L41-L50

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsClopenComponents
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsIrreducibleConnected
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PClopenComponents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_not_mem_zeroLocus_multiIrrelevantIdeal_4f8d0c60fed7 (z : (Σ k, ι k) → ℂ) :
    z ∉ zeroLocus ℂ (multiIrrelevantIdeal ι) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«not_mem_zeroLocus_multiIrrelevantIdeal» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_not_mem_zeroLocus_multiIrrelevantIdeal_4f8d0c60fed7
