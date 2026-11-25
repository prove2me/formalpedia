-- Prove2me | Theorems.Thm_UpperTheory_Small_not_mem_of_dvd_qd
-- name    : UpperTheory.Small.not_mem_of_dvd_qd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:06:51.679137+00:00
-- url     : https://prove2.me/theorems/4a33121d-d8a7-466b-aed9-085a0ba30f20
-- title:
--   Small: not mem of dvd qd
-- statement:
--   The Small construction uses the not mem of dvd qd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/SmallFacts.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/SmallFacts.lean#L20-L25

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

theorem UpperTheory.Small.not_mem_of_dvd_qd {l : ℕ} (hl : l ∣ H.q * H.d) : l ∉ H.small := by sorry
