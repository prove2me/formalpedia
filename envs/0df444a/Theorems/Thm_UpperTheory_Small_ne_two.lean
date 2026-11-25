-- Prove2me | Theorems.Thm_UpperTheory_Small_ne_two
-- name    : UpperTheory.Small.ne_two
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:12:45.978062+00:00
-- url     : https://prove2.me/theorems/203e85d5-9c8f-5102-9d69-ecf2fdab1db0
-- title:
--   Small: ne two
-- statement:
--   The Small construction uses the ne two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/SmallFacts.lean#L16-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/SmallFacts.lean#L16-L18

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

theorem UpperTheory.Small.ne_two {l : ℕ} (h : l ∉ H.small) : l ≠ 2 := by sorry
