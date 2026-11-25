-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_exists_det_ne_zero_bb9babd323db
-- name    : P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_exists_det_ne_zero_bb9babd323db
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T04:17:20.445013+00:00
-- url     : https://prove2.me/theorems/48189a26-3e20-46dd-8b0a-d0f8f4195431
-- title:
--   P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null exists det ne zero bb9babd323db: P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null exists det ne zero bb9babd323db
-- statement:
--   The P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null exists det ne zero bb9babd323db construction uses the P2 M Ground Theory Heights  Heights Rat Sheet No Chart Null exists det ne zero bb9babd323db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetNoChartNull.lean#L97-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/OrbitLimits/PRatSheetNoChartNull.lean#L97-L131

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StRatSheetNoChartNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetOnlyNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCriticalImageNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PRatSheetNoChartNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SheetOnlyNull_exists_det_ne_zero_9afc28185559

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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.RatSheetNoChartNull
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_exists_det_ne_zero_bb9babd323db (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ} {A : Matrix (Fin d) (Fin n) ℂ}
    (hJ : J.IsPrime) (hA : IsFiniteProjection J A)
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : RatChart.IsRatSheetAt J p q x s)
    {W₀ : Set (Fin d → ℂ)} (hW₀ : IsOpen W₀) (hxW₀ : RatChart.ratMap p q x ∈ W₀) :
    ∃ w ∈ W₀, (ReciprocityTheory.AnForm.A.jacC (fun w => A *ᵥ s w) w).det ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RatSheetNoChartNull».«exists_det_ne_zero» := P2M_GroundTheory_Heights__Heights_RatSheetNoChartNull_exists_det_ne_zero_bb9babd323db
