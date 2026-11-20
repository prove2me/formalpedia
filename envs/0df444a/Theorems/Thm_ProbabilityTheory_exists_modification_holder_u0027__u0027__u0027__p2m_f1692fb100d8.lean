-- Prove2me | Theorems.Thm_ProbabilityTheory_exists_modification_holder_u0027__u0027__u0027__p2m_f1692fb100d8
-- name    : ProbabilityTheory.exists_modification_holder_u0027__u0027__u0027__p2m_f1692fb100d8
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T19:34:06.442465+00:00
-- url     : https://prove2.me/theorems/5df29872-2801-4824-b45a-720dea584824
-- title:
--   exists modification holder'''
-- statement:
--   The source theorem `ProbabilityTheory.exists_modification_holder'''` is extracted from `BrownianMotion.Continuity.KolmogorovChentsov`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsov_F003

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

variable [PseudoEMetricSpace T] [PseudoEMetricSpace E]

section HolderSet

end HolderSet

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [hE : Nonempty E]
  [SecondCountableTopology T]

variable [IsFiniteMeasure P]

theorem _root_.ProbabilityTheory.exists_modification_holder_u0027__u0027__u0027__p2m_f1692fb100d8 {C : ℕ → Set T} {c : ℕ → ℝ≥0∞}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : IsKolmogorovProcess X P p q M) (hc : ∀ n, c n ≠ ∞)
    (hd_pos : 0 < d) (hdq_lt : d < q) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t) ∧
      (∀ ω t, ∃ U ∈ 𝓝 t, ∀ (β : ℝ≥0), 0 < β → β < (q - d) / p → ∃ C, HolderOnWith C β (Y · ω) U) ∧
      IsLimitOfIndicator Y X P Set.univ := by sorry
