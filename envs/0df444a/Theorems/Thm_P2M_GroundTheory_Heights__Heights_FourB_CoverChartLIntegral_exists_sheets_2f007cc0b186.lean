-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_exists_sheets_2f007cc0b186
-- name    : P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_exists_sheets_2f007cc0b186
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:47:03.539951+00:00
-- url     : https://prove2.me/theorems/2ac08c04-7993-56eb-8fe6-761ccd75f58c
-- title:
--   P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral exists sheets 2f007cc0b186: P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral exists sheets 2f007cc0b186
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral exists sheets 2f007cc0b186 construction uses the P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral exists sheets 2f007cc0b186 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PCoverChartLIntegral.lean#L31-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PCoverChartLIntegral.lean#L31-L100

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsCoverInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PCoverChartLIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm.M MeasureTheory Topology
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_exists_sheets_2f007cc0b186 {q : X → Fin e → ℂ} {M₀ : Set X} {Δ : Set (Fin e → ℂ)} {d : ℕ}
    (hM : IsOpen M₀) (hΔ : IsClosed Δ) (hmaps : Set.MapsTo q M₀ Δᶜ)
    (hcov : IsCoveringMap hmaps.restrict) (hfib : ∀ z ∉ Δ, (M₀ ∩ q ⁻¹' {z}).encard = d)
    (z : Fin e → ℂ) (hz : z ∉ Δ) :
    ∃ U : Set (Fin e → ℂ), IsOpen U ∧ z ∈ U ∧ U ⊆ Δᶜ ∧ ∃ W : Fin d → Set X,
      (∀ i, IsOpen (W i)) ∧ (∀ i, W i ⊆ M₀) ∧ Pairwise (Function.onFun Disjoint W) ∧
      (∀ x ∈ M₀, q x ∈ U → ∃ i, x ∈ W i) ∧ ∀ i, Set.BijOn q (W i) U := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«CoverChartLIntegral».«exists_sheets» := P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_exists_sheets_2f007cc0b186
