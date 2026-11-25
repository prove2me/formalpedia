-- Prove2me | Theorems.Thm_UpperTheory_Ram_Rd_sqrt_qd_le
-- name    : UpperTheory.Ram.Rd.sqrt_qd_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:01.120836+00:00
-- url     : https://prove2.me/theorems/bfd954d2-d57c-48de-8afc-63c1a81092d4
-- title:
--   Rd: sqrt qd le
-- statement:
--   The Rd construction uses the sqrt qd le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L40-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L40-L48

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

theorem UpperTheory.Ram.Rd.sqrt_qd_le : Real.sqrt ((H.q : ℝ) * H.d) ≤ (H.q : ℝ) * H.d := by sorry
