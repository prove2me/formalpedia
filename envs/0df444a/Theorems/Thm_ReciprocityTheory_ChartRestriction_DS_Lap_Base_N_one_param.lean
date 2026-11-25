-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Base_N_one_param
-- name    : ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.one_param
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:41:31.241397+00:00
-- url     : https://prove2.me/theorems/23e67434-4984-4f3c-9863-e2cd97b7a395
-- title:
--   N: one param
-- statement:
--   The N construction uses the one param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/OneParam.lean#L60-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/LaplaceOperators/LaplaceFoundations/OneParameterSubgroups/OneParam.lean#L60-L192

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_OneParam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Filter Topology
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N

theorem ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.one_param {V H : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (w : H) (hw : ‖w‖ = 1) (φ : V →ₗ[ℂ] H) (d : V →ₗ[ℂ] ℂ) (st : V → V)
    {C Cd Cs K T : ℝ} (hC : 0 ≤ C) (hCd : 0 ≤ Cd) (hCs : 0 ≤ Cs) (hK : 0 ≤ K) (hT : 1 ≤ T)
    (hd : ∀ X, ‖d X‖ ≤ Cd * ‖X‖) (hst : ∀ X, ‖st X‖ ≤ Cs * ‖X‖)
    (hstadd : ∀ X X', st (X + X') = st X + st X') (hdst : ∀ X, d (st X) = starRingEnd ℂ (d X))
    (Yl Yp Ym ρ1 : V) (ρ : ℝ → V) (him : (d Yl).re = 0)
    (hρ : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖ρ τ - Ym - (τ : ℂ) • ρ1‖ ≤ K * τ ^ 2)
    (ha : ‖φ Yp‖ ≤ C) (ha' : ‖φ (st Ym)‖ ≤ C) (hc : ‖φ Yl - ((T : ℂ) * d Yl) • w‖ ≤ C)
    (hall : ∀ X, ‖φ X - ((T : ℂ) * d X) • w‖ ≤ C * Real.sqrt T * ‖X‖)
    (u : ℝ → H →L[ℂ] H) (hu : ∀ s v, ‖u s v‖ = ‖v‖) (hu0 : u 0 w = w)
    (hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt (fun s => ⟪w, u s w⟫_ℂ)
      ⟪w, u s (φ ((((Real.sqrt T)⁻¹ : ℝ) : ℂ) • (Yl + Yp + Ym)))⟫_ℂ s)
    (hmove : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ⟪w, u s (φ Ym)⟫_ℂ = ⟪φ (st (ρ (s / Real.sqrt T))), u s w⟫_ℂ) :
    ‖⟪w, u 1 w⟫_ℂ * cexp (-((Real.sqrt T : ℂ) * d Yl)) - cexp (d ρ1 / 2)‖ ≤
      (3 * C + C * Cs * ‖ρ1‖ + Cd * K + C * Cs * K) / Real.sqrt T * Real.exp ‖d ρ1‖ := by sorry
