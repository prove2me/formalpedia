-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderES_skip_one_eq_succAbove
-- name    : PI.UnitaryGroupMassFormula.QmBorderES.skip_one_eq_succAbove
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:39:45.701876+00:00
-- url     : https://prove2.me/theorems/1d278d7b-bd3f-4efa-94bf-0926ba8104f9
-- title:
--   Qm Border ES: skip one eq succ Above
-- statement:
--   The Qm Border ES construction uses the skip one eq succ Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderSignIdentity/SkipOneEqSuccAbove.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/BorderSignIdentity/SkipOneEqSuccAbove.lean#L12-L15

import Definitions.Def_Formalism_PeriodIntegrals_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_QmRowExp
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderSignIdentity_SkipOneEqSuccAbove
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderES

theorem PI.UnitaryGroupMassFormula.QmBorderES.skip_one_eq_succAbove {t : ℕ} (i : Fin (t + 1)) (j : Fin t) : PI.skip1 i j = i.succAbove j := by sorry
