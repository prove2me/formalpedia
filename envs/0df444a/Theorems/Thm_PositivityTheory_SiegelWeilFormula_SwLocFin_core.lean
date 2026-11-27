-- Prove2me | Theorems.Thm_PositivityTheory_SiegelWeilFormula_SwLocFin_core
-- name    : PositivityTheory.SiegelWeilFormula.SwLocFin.core
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:56:32.639329+00:00
-- url     : https://prove2.me/theorems/8faf5ca1-8604-4676-9c91-26f8fd5a691f
-- title:
--   Sw Loc Fin: core
-- statement:
--   The Sw Loc Fin construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalCharacterIntegrals/DifferentiableSetIntegralFz.lean#L84-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/LocalCharacterIntegrals/DifferentiableSetIntegralFz.lean#L84-L126

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_LocalCharacterIntegrals_DifferentiableSetIntegralFz
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.SiegelWeilFormula PositivityTheory.SiegelWeilFormula.SwLocFin
open MeasureTheory Filter Topology Set
variable {H : Type*} [MeasurableSpace H]

theorem PositivityTheory.SiegelWeilFormula.SwLocFin.core (ν : Measure H) (r : H → ℝ) (u : H → ℂ) (s₀ w₀ : ℂ) (B : ℕ → Set H)
    (hBm : ∀ j, MeasurableSet (B j)) (hmono : Monotone B) (hcov : ⋃ j, B j = univ)
    (hfin : ∀ j, ν (B j) < ⊤) (hr1 : ∀ b, 1 ≤ r b) (hrm : Measurable r) (hrb : ∀ j, ∃ Rm, ∀ b ∈ B j, r b ≤ Rm)
    (hum : AEStronglyMeasurable u ν) (hub : ∃ C, ∀ b, ‖u b‖ ≤ C)
    (hshell : ∀ z j, ∫ b in B (j + 1) \ B j, fz r u s₀ z b ∂ν = 0)
    (hint : ∃ t : ℝ, ∀ z : ℂ, t < z.re → Integrable (fz r u s₀ z) ν)
    (hval : Tendsto (fun j => ∫ b in B j, u b ∂ν) atTop (𝓝 w₀)) :
    ∃ W : ℂ → ℂ, Differentiable ℂ W ∧ W s₀ = w₀ ∧ ∃ t : ℝ, ∀ z : ℂ, t < z.re →
      Integrable (fz r u s₀ z) ν ∧ W z = ∫ b, fz r u s₀ z b ∂ν := by sorry
