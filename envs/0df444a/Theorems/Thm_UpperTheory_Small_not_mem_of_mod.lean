-- Prove2me | Theorems.Thm_UpperTheory_Small_not_mem_of_mod
-- name    : UpperTheory.Small.not_mem_of_mod
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:13:27.294619+00:00
-- url     : https://prove2.me/theorems/bbc399a6-c63c-4335-b581-bbc2e90ddc9c
-- title:
--   Small: not mem of mod
-- statement:
--   The Small construction uses the not mem of mod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/SmallFacts.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/SmallFacts.lean#L36-L42

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

theorem UpperTheory.Small.not_mem_of_mod {l : ℕ} (h : l % (H.QS * H.q * H.d) = 1) : l ∉ H.small := by sorry
