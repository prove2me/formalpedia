-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qh23_uniA_mul_diag
-- name    : UpperTheory.Reformulated.B.Qh23.uniA_mul_diag
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:18:55.50181+00:00
-- url     : https://prove2.me/theorems/7b527e0a-6f07-43b8-8984-9fdf9afbd8a2
-- title:
--   Qh23: uni A mul diag
-- statement:
--   The Qh23 construction uses the uni A mul diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/UniAMulDiag.lean#L3-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/UniAMulDiag.lean#L3-L11

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_UniAMulDiag
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qh23.uniA_mul_diag :
    ∀ {F : Type} [inst : Field F] {k : ℕ} (A B : Matrix (Fin k) (Fin k) F),
    A.BlockTriangular id → B.BlockTriangular id → ∀ (i : Fin k), (A * B) i i = A i i * B i i := by sorry
