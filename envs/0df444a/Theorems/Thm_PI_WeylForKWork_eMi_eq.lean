-- Prove2me | Theorems.Thm_PI_WeylForKWork_eMi_eq
-- name    : PI.WeylForKWork.eMi_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:45:14.949135+00:00
-- url     : https://prove2.me/theorems/2d7877da-0848-48e4-acb9-b917e98f6e3c
-- title:
--   Weyl For KWork: e Mi eq
-- statement:
--   The Weyl For KWork construction uses the e Mi eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L19-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L19-L19

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

theorem PI.WeylForKWork.eMi_eq (ε : Fin N → Bool) (j : Fin (nMi ε)) : eMi ε j = (sMinus ε).orderEmbOfFin rfl j := by sorry
