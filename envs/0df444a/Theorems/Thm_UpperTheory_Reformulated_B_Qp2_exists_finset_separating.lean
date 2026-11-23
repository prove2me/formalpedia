-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qp2_exists_finset_separating
-- name    : UpperTheory.Reformulated.B.Qp2.exists_finset_separating
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:47.528394+00:00
-- url     : https://prove2.me/theorems/e95f1849-d9c8-4169-a3e1-e5c3db44885c
-- title:
--   Qp2: exists finset separating
-- statement:
--   The Qp2 construction uses the exists finset separating property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsFinsetSeparating.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/ExistsFinsetSeparating.lean#L28-L32

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsFinsetSeparating
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qp2.exists_finset_separating :
    ∀ {X : Type} (V : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥V],
    ∃ (T : Finset X), ∀ v ∈ V, (∀ x ∈ T, v x = (0 : ℂ)) → v = (0 : X → ℂ) := by sorry
