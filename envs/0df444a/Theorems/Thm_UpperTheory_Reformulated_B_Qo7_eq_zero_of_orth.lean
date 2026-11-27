-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qo7_eq_zero_of_orth
-- name    : UpperTheory.Reformulated.B.Qo7.eq_zero_of_orth
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:04:28.776534+00:00
-- url     : https://prove2.me/theorems/8e3eb3e1-0d2c-5342-a63f-6445007764f3
-- title:
--   Qo7: eq zero of orth
-- statement:
--   The Qo7 construction uses the eq zero of orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsFurtherExtra.lean#L4-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsFurtherExtra.lean#L4-L86

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsFurtherExtra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

open MeasureTheory

theorem UpperTheory.Reformulated.B.Qo7.eq_zero_of_orth :
    ∀ {K : Type} [inst : TopologicalSpace K] [CompactSpace K]
    [inst_2 : MeasurableSpace K] [BorelSpace K] (μ : MeasureTheory.Measure K) [MeasureTheory.IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure] (S : Set C(K, ℂ)),
    (1 : C(K, ℂ)) ∈ S →
      (∀ a ∈ S, ∀ b ∈ S, a * b ∈ S) →
        (∀ a ∈ S, Star.star a ∈ S) →
          (∀ (x y : K), x ≠ y → ∃ a ∈ S, (a : K → ℂ) x ≠ (a : K → ℂ) y) →
            ∀ (f : C(K, ℂ)), (∀ a ∈ S, ∫ (x : K), (a : K → ℂ) x * (f : K → ℂ) x ∂μ = (0 : ℂ)) → f = (0 : C(K, ℂ)) := by sorry
