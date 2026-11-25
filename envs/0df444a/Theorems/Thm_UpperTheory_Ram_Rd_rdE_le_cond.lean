-- Prove2me | Theorems.Thm_UpperTheory_Ram_Rd_rdE_le_cond
-- name    : UpperTheory.Ram.Rd.rdE_le_cond
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:11:43.502164+00:00
-- url     : https://prove2.me/theorems/31f6f33b-49e5-5ba4-9f8a-569fdfb4aa83
-- title:
--   Rd: rd E le cond
-- statement:
--   The Rd construction uses the rd E le cond property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L58-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L58-L59

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

theorem UpperTheory.Ram.Rd.rdE_le_cond : H.rdE ≤ (H.QS : ℝ) * H.q * H.d := by sorry
