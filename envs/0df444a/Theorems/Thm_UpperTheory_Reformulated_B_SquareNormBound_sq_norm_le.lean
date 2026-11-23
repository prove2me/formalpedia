-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_SquareNormBound_sq_norm_le
-- name    : UpperTheory.Reformulated.B.SquareNormBound.sq_norm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:52.343121+00:00
-- url     : https://prove2.me/theorems/d11ec1b3-c3d6-4c1f-a15a-4655ef98cb79
-- title:
--   Square Norm Bound: sq norm le
-- statement:
--   The Square Norm Bound construction uses the sq norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SquareNormBound.lean#L3-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SquareNormBound.lean#L3-L21

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SquareNormBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.SquareNormBound.sq_norm_le :
    ∀ {m n : ℕ} (x : Fin m → Fin n → ℂ),
    ‖x‖ ^ (2 : ℕ) ≤ ∑ a : Fin m, ∑ i : Fin n, ‖x a i‖ ^ (2 : ℕ) := by sorry
