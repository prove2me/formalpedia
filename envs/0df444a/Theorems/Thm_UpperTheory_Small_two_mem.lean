-- Prove2me | Theorems.Thm_UpperTheory_Small_two_mem
-- name    : UpperTheory.Small.two_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:23:40.958061+00:00
-- url     : https://prove2.me/theorems/0041ad41-6667-4985-a9f7-5f57e0285f5c
-- title:
--   Small: two mem
-- statement:
--   The Small construction uses the two mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/SmallFacts.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/SmallFacts.lean#L10-L14

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

theorem UpperTheory.Small.two_mem : 2 ∈ H.small := by sorry
