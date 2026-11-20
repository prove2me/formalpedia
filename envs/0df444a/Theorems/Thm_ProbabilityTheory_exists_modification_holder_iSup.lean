-- Prove2me | Theorems.Thm_ProbabilityTheory_exists_modification_holder_iSup
-- name    : ProbabilityTheory.exists_modification_holder_iSup
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T15:43:24.43443+00:00
-- url     : https://prove2.me/theorems/1e3f7b42-0a65-4ccb-83c3-84bc4d48086a
-- title:
--   exists modification holder iSup
-- statement:
--   The source theorem `ProbabilityTheory.exists_modification_holder_iSup` is extracted from `BrownianMotion.Continuity.KolmogorovChentsov`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_BrownianMotion_Auxiliary_Topology_F000
import Definitions.Def_BrownianMotion_Auxiliary_Topology_F001
import Definitions.Def_BrownianMotion_Continuity_KolmogorovChentsovInequality_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F002
import Definitions.Def_BrownianMotion_Continuity_LimitModification_F003
import Definitions.Def_BrownianMotion_Gaussian_StochasticProcesses_F000

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

theorem _root_.ProbabilityTheory.exists_modification_holder_iSup {C : ℕ → Set T} {c : ℕ → ℝ≥0∞} {p q : ℕ → ℝ} {M : ℕ → ℝ≥0}
    (hC : IsCoverWithBoundedCoveringNumber C (Set.univ : Set T) c (fun _ ↦ d))
    (hX : ∀ n, IsAEKolmogorovProcess X P (p n) (q n) (M n)) (hc : ∀ n, c n ≠ ∞)
    (hd_pos : 0 < d) (hdq_lt : ∀ n, d < q n) :
    ∃ Y : T → Ω → E, (∀ t, Measurable (Y t)) ∧ (∀ t, Y t =ᵐ[P] X t)
      ∧ ∀ ω t (β : ℝ≥0) (_ : 0 < β) (_ : β < ⨆ n, (q n - d) / (p n)),
        ∃ U ∈ 𝓝 t, ∃ C, HolderOnWith C β (Y · ω) U := by sorry
