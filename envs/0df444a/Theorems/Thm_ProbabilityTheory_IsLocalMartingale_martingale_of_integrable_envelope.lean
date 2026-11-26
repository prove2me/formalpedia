-- Prove2me | Theorems.Thm_ProbabilityTheory_IsLocalMartingale_martingale_of_integrable_envelope
-- name    : ProbabilityTheory.IsLocalMartingale.martingale_of_integrable_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:30:51.86626+00:00
-- url     : https://prove2.me/theorems/2f0b78f0-2643-5343-89d7-90d428da002a
-- title:
--   Local martingale with an integrable compact-time envelope is a martingale
-- statement:
--   A real local martingale with an integrable almost sure bound on every compact time interval is a martingale under the stated filtration assumptions.
-- source:
--   StochLean.Probability.Process.LocalMartingale.Bounded

import Definitions.Def_SourceProof_ee840a5a1d49268537816d0e

open ProbabilityTheory MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {F : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {X : ℝ≥0 → Ω → ℝ}

theorem ProbabilityTheory.IsLocalMartingale.martingale_of_integrable_envelope
    [SigmaFiniteFiltration P F] (hX : IsLocalMartingale X F P)
    (hdom : ∀ T : ℝ≥0, ∃ R : Ω → ℝ, Integrable R P ∧
      ∀ᵐ ω ∂P, ∀ t ≤ T, ‖X t ω‖ ≤ R ω) : Martingale X F P := by sorry
