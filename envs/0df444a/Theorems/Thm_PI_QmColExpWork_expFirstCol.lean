-- Prove2me | Theorems.Thm_PI_QmColExpWork_expFirstCol
-- name    : PI.QmColExpWork.expFirstCol
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:18:09.505546+00:00
-- url     : https://prove2.me/theorems/88b6b263-c76c-4b4d-869c-145fbc70d7d9
-- title:
--   Qm Col Exp Work: exp First Col
-- statement:
--   The Qm Col Exp Work construction uses the exp First Col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialFirstColumn/FirstColumnSplitBijective.lean#L136-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExponentialFirstColumn/FirstColumnSplitBijective.lean#L136-L136

import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialFirstColumn_FirstColumnSplitBijective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open PI PI.QmColExpWork
open Formalism.REAL

theorem PI.QmColExpWork.expFirstCol : PI.ExpFirstCol := by sorry
