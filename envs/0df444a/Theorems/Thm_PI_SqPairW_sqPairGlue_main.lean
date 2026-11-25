-- Prove2me | Theorems.Thm_PI_SqPairW_sqPairGlue_main
-- name    : PI.SqPairW.sqPairGlue_main
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:25:48.316496+00:00
-- url     : https://prove2.me/theorems/b8f8a555-449d-53f8-9cd9-20c0173294e7
-- title:
--   Sq Pair W: sq Pair Glue main
-- statement:
--   The Sq Pair W construction uses the sq Pair Glue main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairGluing/SqPairGlueMain.lean#L56-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SquarePairGluing/SqPairGlueMain.lean#L56-L110

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_ExistsDenLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_SqPairGlueMain
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
open PI PI.SqPairW
open Formalism.L2.PairingIndexBounds.Eq.SqG
variable {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ}

theorem PI.SqPairW.sqPairGlue_main : PI.SqPair.PLocalAll → SplitPairGen := by sorry
