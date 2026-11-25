-- Prove2me | Theorems.Thm_UpperTheory_Ram_Rd_two_mul_rdE_le_cond
-- name    : UpperTheory.Ram.Rd.two_mul_rdE_le_cond
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:11:58.090579+00:00
-- url     : https://prove2.me/theorems/c7dcf6c2-0a19-5708-a8a2-96ccc4deba99
-- title:
--   Rd: two mul rd E le cond
-- statement:
--   The Rd construction uses the two mul rd E le cond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L50-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L50-L56

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FourMulQLeCondN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Ram UpperTheory.Ram.Rd
open Formalism.BasicNotions
variable {R : Ranks} (H : Host R)

theorem UpperTheory.Ram.Rd.two_mul_rdE_le_cond : 2 * H.rdE ≤ (H.QS : ℝ) * H.q * H.d := by sorry
