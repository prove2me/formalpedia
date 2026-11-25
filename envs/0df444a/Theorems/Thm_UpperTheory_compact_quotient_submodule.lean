-- Prove2me | Theorems.Thm_UpperTheory_compact_quotient_submodule
-- name    : UpperTheory.compact_quotient_submodule
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:12:54.695179+00:00
-- url     : https://prove2.me/theorems/281fd78e-122f-4ba7-8253-25e0c5ef90f3
-- title:
--   Upper Theory: compact quotient submodule
-- statement:
--   The Upper Theory construction uses the compact quotient submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CompactQuotientSubmodule.lean#L3-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/CompactQuotientSubmodule.lean#L3-L62

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CompactQuotientSubmodule
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.compact_quotient_submodule :
    ∀ {LL O W Q : Type} [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup W] [Module LL W] [Module O W]
        [IsScalarTower O LL W] [TopologicalSpace LL] [TopologicalSpace W] [ContinuousSMul LL W]
        [IsTopologicalAddGroup W] [T2Space W] [AddCommGroup Q] [Module O Q] [Finite Q]
        (Z : Submodule O W) (p : O) (f : Z →ₗ[O] Q),
        IsCompact (Set.range (algebraMap O LL)) →
        (∀ U ∈ nhds (0 : W), ∃ n : ℕ, ∀ z ∈ Z, p ^ n • z ∈ U) →
        (∀ z : Z, f z = 0 → ∃ w ∈ Z, (z : W) = p • w) →
        Z.FG := by sorry
