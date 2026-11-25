-- Prove2me | Theorems.Thm_PI_SqPairLocal_splitPlace_of
-- name    : PI.SqPairLocal.splitPlace_of
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:25:37.585929+00:00
-- url     : https://prove2.me/theorems/f2b20675-7ad1-439f-b352-7536411f2a8c
-- title:
--   Sq Pair Local: split Place of
-- statement:
--   The Sq Pair Local construction uses the split Place of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SplitPlaceOf.lean#L61-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairLocal/SplitPlaceOf.lean#L61-L120

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IsMaximalComapCj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SplitPlaceOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

theorem PI.SqPairLocal.splitPlace_of (hP : PowLoc) : SplitPlace := by sorry
