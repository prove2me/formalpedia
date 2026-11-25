-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Yxa1_main
-- name    : UpperTheory.Reformulated.B.Yxa1.main
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:12:37.887869+00:00
-- url     : https://prove2.me/theorems/6cc3c517-7824-42fe-85d1-d73268b5c811
-- title:
--   Yxa1: main
-- statement:
--   The Yxa1 construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsTailRest.lean#L3-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ImportsTailRest.lean#L3-L16

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTailRest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Yxa1.main :
    ∀ {α : Type} [inst : MeasurableSpace α] {ν : MeasureTheory.Measure α} {ι : Type} (s : Finset ι)
      (g : ι → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν)),
      (↑(↑(∑ j ∈ s, g j) : α →ₘ[ν] ℂ) : α → ℂ) =ᵐ[ν] fun (x : α) ↦ ∑ j ∈ s, (↑(↑(g j) : α →ₘ[ν] ℂ) : α → ℂ) x := by sorry
