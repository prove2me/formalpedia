-- Prove2me | Theorems.Thm_ProbabilityTheory_finite_set_bound_of_edist_le_of_le_diam_u0027__p2m_c0c43a13c840
-- name    : ProbabilityTheory.finite_set_bound_of_edist_le_of_le_diam_u0027__p2m_c0c43a13c840
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:21:20.33847+00:00
-- url     : https://prove2.me/theorems/4e3b9d1d-1079-4d29-9602-7daef242be9c
-- title:
--   finite set bound of edist le of le diam'
-- statement:
--   The source theorem `ProbabilityTheory.finite_set_bound_of_edist_le_of_le_diam'` is extracted from `BrownianMotion.Continuity.IsKolmogorovProcess`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_IsKolmogorovProcess_F002

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

theorem _root_.ProbabilityTheory.finite_set_bound_of_edist_le_of_le_diam_u0027__p2m_c0c43a13c840 (hJ : HasBoundedCoveringNumber J c d)
    (hJ_finite : J.Finite) (hX : IsAEKolmogorovProcess X P p q M)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hdq_lt : d < q)
    (hδ : δ ≠ 0) (hδ_le : δ / 4 ≤ Metric.ediam J) :
    ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P
      ≤ 2 ^ (2 * p + 4 * q + 1) * M * c * δ ^ (q - d)
        * (4 ^ d * (ENNReal.ofReal (Real.logb 2 (c.toReal * 4 ^ d * δ.toReal⁻¹ ^ d))) ^ q
            + Cp d p q) := by sorry
