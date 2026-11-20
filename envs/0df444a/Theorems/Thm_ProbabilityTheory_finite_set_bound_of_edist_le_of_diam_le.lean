-- Prove2me | Theorems.Thm_ProbabilityTheory_finite_set_bound_of_edist_le_of_diam_le
-- name    : ProbabilityTheory.finite_set_bound_of_edist_le_of_diam_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:20:25.869758+00:00
-- url     : https://prove2.me/theorems/c692a8d7-0e11-4aba-a086-a32dab02c33d
-- title:
--   finite set bound of edist le of diam le
-- statement:
--   The source theorem `ProbabilityTheory.finite_set_bound_of_edist_le_of_diam_le` is extracted from `BrownianMotion.Continuity.IsKolmogorovProcess`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F002
import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F003

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Stochastic processes satisfying the Kolmogorov condition

-/

@[expose] public section

open MeasureTheory Metric
open scoped ENNReal NNReal Finset

section Aux

end Aux

namespace ProbabilityTheory

variable {T Ω E : Type*} [PseudoEMetricSpace T] {mΩ : MeasurableSpace Ω}
  [PseudoEMetricSpace E]
  {p q : ℝ} {M : ℝ≥0} {P : Measure Ω} {X : T → Ω → E}

section Measurability

variable [MeasurableSpace E] [BorelSpace E]

end Measurability

section FirstTerm

variable {J : Set T}

end FirstTerm

section SecondTerm

variable {J : Set T} {C : ℕ → Finset T} {ε : ℕ → ℝ≥0} {j k m : ℕ}

end SecondTerm

section Together

variable {M : ℝ≥0} {d p q : ℝ} {J : Set T} {c : ℝ≥0∞} {δ : ℝ≥0}

theorem _root_.ProbabilityTheory.finite_set_bound_of_edist_le_of_diam_le (hJ : HasBoundedCoveringNumber J c d)
    (hJ_finite : J.Finite) (hX : IsAEKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hdq_lt : d < q) (hδ_le : Metric.ediam J ≤ δ / 4) :
    ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ}), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 4 ^ p * 2 ^ q * M * c * δ ^ (q - d) * Cp d p q := by sorry
