-- Prove2me | Theorems.Thm_UpperTheory_Small_localLevel_eq_one_of_not_mem_smallPrimes
-- name    : UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:49:13.045602+00:00
-- url     : https://prove2.me/theorems/38c5e0f6-5495-5ca8-9d6b-0165246e8162
-- title:
--   Small: local Level eq one of not mem small Primes
-- statement:
--   The Small construction uses the local Level eq one of not mem small Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/SmallFacts.lean#L53-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/SmallFacts.lean#L53-L54

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_SmallFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Small
open Formalism.BasicNotions
variable {R : Ranks} (H : Host R)
variable {H}

theorem UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (h : N.l i ∉ H.small) : N.s0 i = 1 := by sorry
