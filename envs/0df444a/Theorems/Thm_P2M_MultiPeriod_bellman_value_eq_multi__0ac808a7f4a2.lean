-- Prove2me | Theorems.Thm_P2M_MultiPeriod_bellman_value_eq_multi__0ac808a7f4a2
-- name    : P2M_MultiPeriod_bellman_value_eq_multi__0ac808a7f4a2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:15:20.119809+00:00
-- url     : https://prove2.me/theorems/6d8933c3-2741-418b-8c1c-4b95ed664fc3
-- title:
--   P2 M Multi Period bellman value eq multi  0ac808a7f4a2: P2 M Multi Period bellman value eq multi  0ac808a7f4a2
-- statement:
--   **Multi-period Bellman value representation, probability-kernel
--       form.**  `bellman_value_eq_multi` with the nonemptiness hypothesis
--       `hne` replaced by the probability hypothesis on the `Y`-side kernel
--       (the `X`-side one was already assumed): nonemptiness of every `Feas`
--       fiber follows via `Feas.nonempty`.
--
--   Source: https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/FeasNonempty.lean#L145-L156
-- source:
--   https://github.com/MaxWellApexLab/BicausalOT-palomar/blob/3fe500ff64a75d7ab71b474d0c656d5471f62992/BicausalOT/FeasNonempty.lean#L145-L156

import Definitions.Def_BicausalOT_MultiPeriod
import Definitions.Def_BicausalOT_ValueRepresentation
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_BicausalOT_FeasNonempty
set_option autoImplicit false
open MeasureTheory Set ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
variable [∀ n, MeasurableSpace (X n)] [∀ n, MeasurableSpace (Y n)]
variable (κμ : (t : ℕ) → XHist X t → Measure (X (t + 1)))
variable (κν : (t : ℕ) → YHist Y t → Measure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)

theorem P2M_MultiPeriod_bellman_value_eq_multi__0ac808a7f4a2 (T : ℕ)
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure (Y 0)) [IsProbabilityMeasure ν₀]
    (hκμ : ∀ t x, IsProbabilityMeasure (κμ t x))
    (hκν : ∀ t y, IsProbabilityMeasure (κν t y)) :
    ⨅ (γ₀ : Measure (X 0 × Y 0)) (γ : Strat X Y)
      (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀)
      (_ : ∀ t h, γ t h ∈ Feas κμ κν t h),
      ∫⁻ h₀, costGo c γ T 0 h₀ ∂γ₀
    = ⨅ (γ₀ : Measure (X 0 × Y 0)) (_ : γ₀ ∈ CouplingSet₀ μ₀ ν₀),
      ∫⁻ h₀, VGo c κμ κν T 0 h₀ ∂γ₀ := by sorry

alias «MultiPeriod».«bellman_value_eq_multi'» := P2M_MultiPeriod_bellman_value_eq_multi__0ac808a7f4a2
