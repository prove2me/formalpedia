-- Prove2me | Theorems.Thm_UpperTheory_Ram_Rd_one_le_QS_real
-- name    : UpperTheory.Ram.Rd.one_le_QS_real
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:32:44.399639+00:00
-- url     : https://prove2.me/theorems/851e8d93-3aed-44c8-bcc0-a42e3bf21bde
-- title:
--   Rd: one le QS real
-- statement:
--   The Rd construction uses the one le QS real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L16-L16

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

theorem UpperTheory.Ram.Rd.one_le_QS_real : (1 : ℝ) ≤ H.QS := by sorry
