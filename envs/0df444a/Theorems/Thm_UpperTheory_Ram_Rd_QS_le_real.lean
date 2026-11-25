-- Prove2me | Theorems.Thm_UpperTheory_Ram_Rd_QS_le_real
-- name    : UpperTheory.Ram.Rd.QS_le_real
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:11:46.995635+00:00
-- url     : https://prove2.me/theorems/2f240cff-3688-5e8f-b505-b5f9233cb6d0
-- title:
--   Rd: QS le real
-- statement:
--   The Rd construction uses the QS le real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L18-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L18-L18

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

theorem UpperTheory.Ram.Rd.QS_le_real : (H.QS : ℝ) ≤ (R.n : ℝ) ^ 2 := by sorry
