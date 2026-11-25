-- Prove2me | Theorems.Thm_Reformulated_AlgebraicInfinityType_InfinityType_isAlgebraic_iff_twist
-- name    : Reformulated.AlgebraicInfinityType.InfinityType.isAlgebraic_iff_twist
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:37:49.373908+00:00
-- url     : https://prove2.me/theorems/a3fb8e65-11fe-57ac-ab90-f5fbfcea7a90
-- title:
--   Infinity Type: is Algebraic iff twist
-- statement:
--   The Infinity Type construction uses the is Algebraic iff twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/AlgebraicInfinityType/InfinityType.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/AlgebraicInfinityType/InfinityType.lean#L46-L51

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_AlgebraicInfinityType_InfinityType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Reformulated Reformulated.AlgebraicInfinityType
open NumberField
open Reformulated.AlgebraicInfinityType.InfinityType
variable {F : Type*} [Field F] {n : ℕ}

theorem Reformulated.AlgebraicInfinityType.InfinityType.isAlgebraic_iff_twist (t : InfinityType F n) :
    t.IsAlgebraic ↔ (t.twist ((1 - (n : ℂ)) / 2)).IsLAlgebraic := by sorry
