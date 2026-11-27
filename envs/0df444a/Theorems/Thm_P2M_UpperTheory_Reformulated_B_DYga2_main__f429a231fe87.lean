-- Prove2me | Theorems.Thm_P2M_UpperTheory_Reformulated_B_DYga2_main__f429a231fe87
-- name    : P2M_UpperTheory_Reformulated_B_DYga2_main__f429a231fe87
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:44:02.016116+00:00
-- url     : https://prove2.me/theorems/8ad71ad5-2b78-4ec0-97df-be7a82e12471
-- title:
--   P2 M Upper Theory Reformulated B DYga2 main  f429a231fe87: P2 M Upper Theory Reformulated B DYga2 main  f429a231fe87
-- statement:
--   The P2 M Upper Theory Reformulated B DYga2 main  f429a231fe87 construction uses the P2 M Upper Theory Reformulated B DYga2 main  f429a231fe87 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsExtra.lean#L3-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsExtra.lean#L3-L132

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsExtra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem P2M_UpperTheory_Reformulated_B_DYga2_main__f429a231fe87.{u_1} :
    ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [FiniteDimensional ℝ E]
      [inst_3 : MeasurableSpace E] [BorelSpace E] (μ : MeasureTheory.Measure E) [μ.IsAddHaarMeasure] {A : ℕ},
      Module.finrank ℝ E < A →
        (0 : ℕ) < Module.finrank ℝ E →
          ∃ (c : ℝ),
            (0 : ℝ) ≤ c ∧
              ∀ (η : ℝ),
                (0 : ℝ) < η →
                  ∀ (F : Finset E),
                    (∀ y ∈ F, ∀ y' ∈ F, y ≠ y' → η ≤ ‖y - y'‖ ^ Module.finrank ℝ E) →
                      ∑ y ∈ F, (((1 : ℝ) + ‖y‖) ^ A)⁻¹ ≤ c * ((1 : ℝ) + η⁻¹) := by sorry

alias «UpperTheory».«Reformulated».«B».«DYga2».«main».«» := P2M_UpperTheory_Reformulated_B_DYga2_main__f429a231fe87
