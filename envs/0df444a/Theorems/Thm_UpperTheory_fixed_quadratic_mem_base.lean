-- Prove2me | Theorems.Thm_UpperTheory_fixed_quadratic_mem_base
-- name    : UpperTheory.fixed_quadratic_mem_base
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:48.82606+00:00
-- url     : https://prove2.me/theorems/26af064d-6010-43a2-a5ec-14ef35703ba1
-- title:
--   Upper Theory: fixed quadratic mem base
-- statement:
--   The Upper Theory construction uses the fixed quadratic mem base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FixedQuadraticMemBase.lean#L3-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/FixedQuadraticMemBase.lean#L3-L39

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FixedQuadraticMemBase
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.fixed_quadratic_mem_base :
    ∀ {F E : Type} [Field F] [Field E] [Algebra F E], Module.finrank F E = 2 → ∀ (σ : E →ₐ[F] E) (α : E), σ α ≠ α → ∀ x, σ x = x → x ∈ (algebraMap F E).range := by sorry
