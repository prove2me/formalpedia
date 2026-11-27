-- Prove2me | Theorems.Thm_UpperTheory_Small_not_mem_of_qd
-- name    : UpperTheory.Small.not_mem_of_qd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:49:20.289119+00:00
-- url     : https://prove2.me/theorems/aa8fd30d-a55e-525c-9b1d-a18428d42d17
-- title:
--   Small: not mem of qd
-- statement:
--   The Small construction uses the not mem of qd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/SmallFacts.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/SmallFacts.lean#L31-L34

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

theorem UpperTheory.Small.not_mem_of_qd {l : ℕ} (hl : l = H.q ∨ l = H.d) : l ∉ H.small := by sorry
