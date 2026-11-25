-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Qk24_aux2
-- name    : UpperTheory.Reformulated.B.Qk24.aux2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:03:25.086045+00:00
-- url     : https://prove2.me/theorems/71098425-67a3-48a2-9259-34b9f1718002
-- title:
--   Qk24: aux2
-- statement:
--   The Qk24 construction uses the aux2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SignActionMapComm.lean#L6-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/SignActionMapComm.lean#L6-L9

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SignActionMapComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Qk24.aux2 :
    ∀ (I : Formalism.MainNotions.S.AutInst), IsFractionRing (NumberField.RingOfIntegers I.F) I.F := by sorry
