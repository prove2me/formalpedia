-- Prove2me | Theorems.Thm_ProbabilityTheory_constL_lt_top
-- name    : ProbabilityTheory.constL_lt_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:25:00.099321+00:00
-- url     : https://prove2.me/theorems/6c605e77-3c09-429e-80b1-74452bcc3d9d
-- title:
--   constL lt top
-- statement:
--   The source theorem `ProbabilityTheory.constL_lt_top` is extracted from `BrownianMotion.Continuity.KolmogorovChentsovInequality`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
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

theorem _root_.ProbabilityTheory.constL_lt_top (hT : Metric.ediam U < ∞)
    (hc : c ≠ ∞) (hd_pos : 0 < d) (hp_pos : 0 < p) (hdq_lt : d < q) (hβ_lt : β < (q - d) / p) :
    constL T c d p q β U < ∞ := by sorry
