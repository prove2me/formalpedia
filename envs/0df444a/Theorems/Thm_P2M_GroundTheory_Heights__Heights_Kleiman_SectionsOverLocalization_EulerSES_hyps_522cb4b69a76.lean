-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_hyps_522cb4b69a76
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_hyps_522cb4b69a76
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:27:45.288272+00:00
-- url     : https://prove2.me/theorems/e5da62da-025b-4f01-8461-682c6528f69d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES hyps 522cb4b69a76: P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES hyps 522cb4b69a76
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES hyps 522cb4b69a76 construction uses the P2 M Ground Theory Heights  Heights Kleiman Sections Over Localization Euler SES hyps 522cb4b69a76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DegZero.lean#L52-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/DegZero.lean#L52-L87

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_DegZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
noncomputable section
open EulerSES

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_hyps_522cb4b69a76 :
    let CA : ∀ _ : ℕ, Submodule ℚ ℚ := fun _ => ⊥
    let CB : ∀ _ : ℕ, Submodule ℚ ℚ := EulerSES.degZero
    let d : ∀ n : ℕ, (fun _ : ℕ => ℚ) n →ₗ[ℚ] (fun _ : ℕ => ℚ) (n + 1) := fun _ => 0
    let f : ∀ n : ℕ, (fun _ : ℕ => ℚ) n →ₗ[ℚ] (fun _ : ℕ => ℚ) n := fun _ => 0
    let g : ∀ n : ℕ, (fun _ : ℕ => ℚ) n →ₗ[ℚ] (fun _ : ℕ => ℚ) n := fun _ => LinearMap.id
    (∀ n, ∀ x ∈ CA n, d n x ∈ CA (n + 1)) ∧ (∀ n, ∀ x ∈ CB n, d n x ∈ CB (n + 1)) ∧
    (∀ n, ∀ x ∈ CA n, d (n + 1) (d n x) = 0) ∧ (∀ n, ∀ x ∈ CB n, d (n + 1) (d n x) = 0) ∧
    (∀ n, ∀ x ∈ CA n, f n x ∈ CB n) ∧ (∀ n, ∀ y ∈ CB n, g n y ∈ CB n) ∧
    (∀ n, ∀ x ∈ CA n, d n (f n x) = f (n + 1) (d n x)) ∧
    (∀ n, ∀ y ∈ CB n, d n (g n y) = g (n + 1) (d n y)) ∧
    (∀ n, ∀ x ∈ CA n, f n x = 0 → x = 0) ∧
    (∀ n, ∀ x ∈ CA n, g n (f n x) = 0) ∧
    (∀ n, ∀ y ∈ CB n, g n y = 0 → ∃ x ∈ CA n, f n x = y) ∧
    (∀ n, ∀ z ∈ CB n, ∃ y ∈ CB n, g n y = z) ∧
    (∀ n, FiniteDimensional ℚ (coh CA d n)) ∧ (∀ n, FiniteDimensional ℚ (coh CB d n)) ∧
    Subsingleton (coh CA d 1) ∧ Module.finrank ℚ (coh CB d 0) = 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SectionsOverLocalization».«EulerSES».«hyps» := P2M_GroundTheory_Heights__Heights_Kleiman_SectionsOverLocalization_EulerSES_hyps_522cb4b69a76
