-- Prove2me | Theorems.Thm_PI_WeylForKWork_ePl_eq
-- name    : PI.WeylForKWork.ePl_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:44:15.69152+00:00
-- url     : https://prove2.me/theorems/fbf33d0d-69af-48ff-a1fb-384fd71360bb
-- title:
--   Weyl For KWork: e Pl eq
-- statement:
--   The Weyl For KWork construction uses the e Pl eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L17-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L17-L17

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_Formula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork
open PI PI.UpqRep Matrix Finset
variable {N : ℕ}

theorem PI.WeylForKWork.ePl_eq (ε : Fin N → Bool) (i : Fin (nPl ε)) : ePl ε i = (sPlus ε).orderEmbOfFin rfl i := by sorry
