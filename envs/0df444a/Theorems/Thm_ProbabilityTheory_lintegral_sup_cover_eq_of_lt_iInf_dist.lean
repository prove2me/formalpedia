-- Prove2me | Theorems.Thm_ProbabilityTheory_lintegral_sup_cover_eq_of_lt_iInf_dist
-- name    : ProbabilityTheory.lintegral_sup_cover_eq_of_lt_iInf_dist
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:19:31.451623+00:00
-- url     : https://prove2.me/theorems/87511632-cd64-4633-99c2-dea2841bced3
-- title:
--   lintegral sup cover eq of lt iInf dist
-- statement:
--   The source theorem `ProbabilityTheory.lintegral_sup_cover_eq_of_lt_iInf_dist` is extracted from `BrownianMotion.Continuity.IsKolmogorovProcess`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

theorem _root_.ProbabilityTheory.lintegral_sup_cover_eq_of_lt_iInf_dist {C : Set T} {ε : ℝ≥0}
    (hX : IsAEKolmogorovProcess X P p q M)
    (hJ : J.Finite) (hC : IsCover ε J C) (hC_subset : C ⊆ J)
    (hε_lt : ε < ⨅ (s : J) (t : J) (_h : 0 < edist s t), edist s t) :
    ∫⁻ ω, ⨆ (s : C) (t : { t : C // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P
      = ∫⁻ ω, ⨆ (s : J) (t : { t : J // edist s t ≤ δ }), edist (X s ω) (X t ω) ^ p ∂P := by sorry
