-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qh16_inP_apply_eq_zero
-- name    : UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:34:22.124815+00:00
-- url     : https://prove2.me/theorems/9519bc26-33e5-4147-9957-639b72f938a6
-- title:
--   Qh16: in P apply eq zero
-- statement:
--   The Qh16 construction uses the in P apply eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InPApplyEqZero.lean#L17-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InPApplyEqZero.lean#L17-L26

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InPApplyEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero :
    ∀ {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ},
      UpperTheory.Reformulated.B.Qh16.inP ε X → ∀ {a b : Fin n}, ε a = ε b → X a b = (0 : ℂ) := by sorry
