-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NineStatements_abs_degree_sub_le_caf889cc4611
-- name    : P2M_GroundTheory_Heights__Heights_NineStatements_abs_degree_sub_le_caf889cc4611
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T04:04:30.990054+00:00
-- url     : https://prove2.me/theorems/5abb6a99-47b3-5716-9e9a-7894a8609691
-- title:
--   P2 M Ground Theory Heights  Heights Nine Statements abs degree sub le caf889cc4611: P2 M Ground Theory Heights  Heights Nine Statements abs degree sub le caf889cc4611
-- statement:
--   The P2 M Ground Theory Heights  Heights Nine Statements abs degree sub le caf889cc4611 construction uses the P2 M Ground Theory Heights  Heights Nine Statements abs degree sub le caf889cc4611 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigen.lean#L70-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/StabilizerCovolume/RecordEigen.lean#L70-L89

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigenInputs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_StabilizerCovolume_RecordEigen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open NumberField IsDedekindDomain
open scoped nonZeroDivisors

theorem P2M_GroundTheory_Heights__Heights_NineStatements_abs_degree_sub_le_caf889cc4611 {L : Type} [Field L] [NumberField L] {Ψ : Type} [Fintype Ψ]
    (P : SmallBlockLattices L Ψ) (lat₁ lat₂ : Ψ → FractionalIdeal (𝓞 L)⁰ L) (h₁ : ∀ τ, lat₁ τ ≠ 0)
    (h₂ : ∀ τ, lat₂ τ ≠ 0) (K : ℝ)
    (hx : ∀ τ, |Real.log (FractionalIdeal.absNorm (lat₁ τ * (lat₂ τ)⁻¹) : ℝ)| ≤ Module.finrank ℚ L * K) :
    |P.degree lat₁ - P.degree lat₂| ≤ Fintype.card Ψ * K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NineStatements».«abs_degree_sub_le» := P2M_GroundTheory_Heights__Heights_NineStatements_abs_degree_sub_le_caf889cc4611
