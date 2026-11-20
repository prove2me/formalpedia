-- Prove2me | Theorems.Thm_ProbabilityTheory_lintegral_div_edist_le_sum_integral_edist_le
-- name    : ProbabilityTheory.lintegral_div_edist_le_sum_integral_edist_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:23:07.087402+00:00
-- url     : https://prove2.me/theorems/5d14476d-5d06-4b00-9b73-4f7870f88ea2
-- title:
--   lintegral div edist le sum integral edist le
-- statement:
--   The source theorem `ProbabilityTheory.lintegral_div_edist_le_sum_integral_edist_le` is extracted from `BrownianMotion.Continuity.KolmogorovChentsovInequality`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F000

/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

/-!
# Kolmogorov-Chentsov theorem

-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology Asymptotics

section aux

end aux

namespace ProbabilityTheory

variable {T Ω E : Type*} {mΩ : MeasurableSpace Ω}
  {X : T → Ω → E} {c : ℝ≥0∞} {d p q : ℝ} {M β : ℝ≥0} {P : Measure Ω}
  {U : Set T}

section PseudoEMetricSpace

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E] [MeasurableSpace E] [BorelSpace E]

theorem _root_.ProbabilityTheory.lintegral_div_edist_le_sum_integral_edist_le (hT : Metric.ediam U < ∞)
    (hX : IsAEKolmogorovProcess X P p q M)
    (hβ : 0 < β) {J : Set T} [Countable J] (hJU : J ⊆ U) :
    ∫⁻ ω, ⨆ (s : J) (t : J), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
      ≤ ∑' (k : ℕ), 2 ^ (k * β * p)
          * ∫⁻ ω, ⨆ (s : J)
              (t : {t : J // edist s t ≤ 2 * 2⁻¹ ^ k * (Metric.ediam U + 1)}),
                edist (X s ω) (X t ω) ^p ∂P := by sorry
