-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_isOpen_image_of_cover_3f74170e1f04
-- name    : P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_isOpen_image_of_cover_3f74170e1f04
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:41:32.766596+00:00
-- url     : https://prove2.me/theorems/68cc4237-8d59-558a-b8a5-ae6443ed8810
-- title:
--   P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral is Open image of cover 3f74170e1f04: P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral is Open image of cover 3f74170e1f
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral is Open image of cover 3f74170e1f04 construction uses the P2 M Ground Theory Heights  Heights Four B Cover Chart LIntegral is Open image of cover 3f74170e1f04 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PCoverChartLIntegral.lean#L17-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PCoverChartLIntegral.lean#L17-L29

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

theorem P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_isOpen_image_of_cover_3f74170e1f04 {q : X → Fin e → ℂ} {M₀ : Set X} {Δ : Set (Fin e → ℂ)}
    (hΔ : IsClosed Δ) (hmaps : Set.MapsTo q M₀ Δᶜ) (hcov : IsCoveringMap hmaps.restrict)
    (O : Set X) (hO : IsOpen O) (hOM : O ⊆ M₀) : IsOpen (q '' O) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«CoverChartLIntegral».«isOpen_image_of_cover» := P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_isOpen_image_of_cover_3f74170e1f04
