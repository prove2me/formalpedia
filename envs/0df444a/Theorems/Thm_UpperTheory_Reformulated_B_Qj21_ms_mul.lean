-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qj21_ms_mul
-- name    : UpperTheory.Reformulated.B.Qj21.ms_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:22:21.993717+00:00
-- url     : https://prove2.me/theorems/3a4e5c9f-7329-4061-94e3-ee31c8d6964b
-- title:
--   Qj21: ms mul
-- statement:
--   The Qj21 construction uses the ms mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MsMul.lean#L40-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/MsMul.lean#L40-L56

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MsMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qj21.ms_mul :
    ∀ {H : Type} {N0 N1 : ℕ} (t : H) {a b a' b' : ℕ} {P Q : UpperTheory.Reformulated.B.Qj21.PolyXZ H N0 N1},
      P ∈ UpperTheory.Reformulated.B.Qj21.MS t a b → Q ∈ UpperTheory.Reformulated.B.Qj21.MS t a' b' → P * Q ∈ UpperTheory.Reformulated.B.Qj21.MS t (a + a') (b + b') := by sorry
