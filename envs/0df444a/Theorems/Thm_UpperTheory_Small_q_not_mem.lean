-- Prove2me | Theorems.Thm_UpperTheory_Small_q_not_mem
-- name    : UpperTheory.Small.q_not_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:48:27.783717+00:00
-- url     : https://prove2.me/theorems/e44cf5a9-706f-4f9b-83fc-01b0dca184e8
-- title:
--   Small: q not mem
-- statement:
--   The Small construction uses the q not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/SmallFacts.lean#L27-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/SmallFacts.lean#L27-L27

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

theorem UpperTheory.Small.q_not_mem : H.q ∉ H.small := by sorry
