-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qi20_mulVec_fix_of_supp
-- name    : UpperTheory.Reformulated.B.Qi20.mulVec_fix_of_supp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:35.574782+00:00
-- url     : https://prove2.me/theorems/0b526d1c-7646-4b14-b0fe-3a06b9f09328
-- title:
--   Qi20: mul Vec fix of supp
-- statement:
--   The Qi20 construction uses the mul Vec fix of supp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MulVecFixOfSupp.lean#L3-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MulVecFixOfSupp.lean#L3-L14

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulVecFixOfSupp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qi20.mulVec_fix_of_supp :
    ∀ {m : ℕ} (y : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ),
    (∀ (j : Fin m), v j ≠ (0 : ℂ) → ∀ (i : Fin m), y i j = if i = j then (1 : ℂ) else (0 : ℂ)) → y.mulVec v = v := by sorry
