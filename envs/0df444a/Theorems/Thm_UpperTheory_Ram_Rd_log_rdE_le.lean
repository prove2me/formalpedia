-- Prove2me | Theorems.Thm_UpperTheory_Ram_Rd_log_rdE_le
-- name    : UpperTheory.Ram.Rd.log_rdE_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:11:36.036858+00:00
-- url     : https://prove2.me/theorems/a892c99e-0c94-5382-b78a-6439311d011a
-- title:
--   Rd: log rd E le
-- statement:
--   The Rd construction uses the log rd E le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L61-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L61-L74

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

theorem UpperTheory.Ram.Rd.log_rdE_le : Real.log H.rdE ≤ 2 * Real.log R.n + (Real.log H.q + Real.log H.d) / 2 := by sorry
