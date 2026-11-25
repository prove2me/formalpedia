-- Prove2me | Theorems.Thm_UpperTheory_Ram_Rd_rdE_pos
-- name    : UpperTheory.Ram.Rd.rdE_pos
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:12:16.879469+00:00
-- url     : https://prove2.me/theorems/10cc97c5-e99f-4f15-80df-1cfe2bc77e02
-- title:
--   Rd: rd E pos
-- statement:
--   The Rd construction uses the rd E pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L36-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L36-L36

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

theorem UpperTheory.Ram.Rd.rdE_pos : 0 < H.rdE := by sorry
