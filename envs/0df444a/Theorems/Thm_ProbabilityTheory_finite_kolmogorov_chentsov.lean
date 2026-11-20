-- Prove2me | Theorems.Thm_ProbabilityTheory_finite_kolmogorov_chentsov
-- name    : ProbabilityTheory.finite_kolmogorov_chentsov
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T12:25:29.363023+00:00
-- url     : https://prove2.me/theorems/b0737948-dec7-40d2-9811-1ece48011858
-- title:
--   finite kolmogorov chentsov
-- statement:
--   The source theorem `ProbabilityTheory.finite_kolmogorov_chentsov` is extracted from `BrownianMotion.Continuity.KolmogorovChentsovInequality`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F001

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

theorem _root_.ProbabilityTheory.finite_kolmogorov_chentsov
    (hT : HasBoundedCoveringNumber U c d)
    (hX : IsAEKolmogorovProcess X P p q M)
    (hd_pos : 0 < d) (hdq_lt : d < q)
    (hβ_pos : 0 < β) (T' : Set T) [hT' : Finite T'] (hT'U : T' ⊆ U) :
    ∫⁻ ω, ⨆ (s : T') (t : T'), edist (X s ω) (X t ω) ^ p / edist s t ^ (β * p) ∂P
      ≤ M * constL T c d p q β U := by sorry
