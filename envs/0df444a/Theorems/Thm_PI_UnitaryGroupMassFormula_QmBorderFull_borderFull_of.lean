-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_borderFull_of
-- name    : PI.UnitaryGroupMassFormula.QmBorderFull.borderFull_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:55.988083+00:00
-- url     : https://prove2.me/theorems/1f0f6cbd-5175-46f2-be13-012c2d0ebc00
-- title:
--   Qm Border Full: border Full of
-- statement:
--   The Qm Border Full construction uses the border Full of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/Development.lean#L69-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderMinorRotation/Development.lean#L69-L110

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderFull
import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_QmSkip
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull
open PI

theorem PI.UnitaryGroupMassFormula.QmBorderFull.borderFull_of (hFC : ExpFirstCol) (hS : BorderS) (hM : BFMid) : BorderFull := by sorry
