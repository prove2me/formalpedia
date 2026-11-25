-- Prove2me | Theorems.Thm_UpperTheory_Ram_Rd_log_cond_le
-- name    : UpperTheory.Ram.Rd.log_cond_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:56:28.954498+00:00
-- url     : https://prove2.me/theorems/a0f4787b-a93d-4cf8-98f1-4342dd08e697
-- title:
--   Rd: log cond le
-- statement:
--   The Rd construction uses the log cond le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L76-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L76-L83

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

theorem UpperTheory.Ram.Rd.log_cond_le : Real.log ((H.QS : ℝ) * H.q * H.d) ≤ 2 * Real.log R.n + Real.log H.q + Real.log H.d := by sorry
