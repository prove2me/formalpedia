-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_MultiDimensional_multi_dim
-- name    : UpperTheory.Reformulated.B.MultiDimensional.multi_dim
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:20.897914+00:00
-- url     : https://prove2.me/theorems/3ad0066f-54a0-42d4-88e6-f2373254a496
-- title:
--   Multi Dimensional: multi dim
-- statement:
--   The Multi Dimensional construction uses the multi dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MultiDimensional.lean#L3-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MultiDimensional.lean#L3-L16

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MultiDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.MultiDimensional.multi_dim :
    ∀ {P : Type} [inst : Fintype P] (g : P → ℤ → ENNReal), ∑' (x : P → ℤ), ∏ p : P, g p (x p) ≤ ∏ p : P, ∑' (n : ℤ), g p n := by sorry
