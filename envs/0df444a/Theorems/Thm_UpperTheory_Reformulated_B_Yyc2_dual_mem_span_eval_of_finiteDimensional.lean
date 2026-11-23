-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Yyc2_dual_mem_span_eval_of_finiteDimensional
-- name    : UpperTheory.Reformulated.B.Yyc2.dual_mem_span_eval_of_finiteDimensional
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:19.975335+00:00
-- url     : https://prove2.me/theorems/5331f535-793d-4b24-82af-bb5930ccdf85
-- title:
--   Yyc2: dual mem span eval of finite Dimensional
-- statement:
--   The Yyc2 construction uses the dual mem span eval of finite Dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DualMemSpanEvalOfFiniteDimensional.lean#L3-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/DualMemSpanEvalOfFiniteDimensional.lean#L3-L14

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DualMemSpanEvalOfFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Yyc2.dual_mem_span_eval_of_finiteDimensional :
    ∀ {Y : Type} (E : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ ↥E] (φ : Module.Dual ℂ ↥E),
      φ ∈ Submodule.span ℂ (Set.range fun (y : Y) ↦ LinearMap.proj y ∘ₗ E.subtype) := by sorry
