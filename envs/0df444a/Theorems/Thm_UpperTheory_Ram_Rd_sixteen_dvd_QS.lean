-- Prove2me | Theorems.Thm_UpperTheory_Ram_Rd_sixteen_dvd_QS
-- name    : UpperTheory.Ram.Rd.sixteen_dvd_QS
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:46:13.308012+00:00
-- url     : https://prove2.me/theorems/a069f77b-20bb-403e-acc4-bf921ff76051
-- title:
--   Rd: sixteen dvd QS
-- statement:
--   The Rd construction uses the sixteen dvd QS property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/RamifiedDiscriminants/FourMulQLeCondN.lean#L10-L14

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_HostCls
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_RamifiedDiscriminants_FourMulQLeCondN
import Theorems.Thm_Formalism_HC_HostRaw_sixteen_dvd_QS

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

theorem UpperTheory.Ram.Rd.sixteen_dvd_QS : 16 ∣ H.QS := by sorry
