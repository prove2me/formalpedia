-- Prove2me | Theorems.Thm_PI_WeylForKWork_eMi_ne_ePl
-- name    : PI.WeylForKWork.eMi_ne_ePl
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T08:46:06.415745+00:00
-- url     : https://prove2.me/theorems/2b3a3f60-ab31-59f7-8e93-2bf57f1e1e44
-- title:
--   Weyl For KWork: e Mi ne e Pl
-- statement:
--   The Weyl For KWork construction uses the e Mi ne e Pl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L47-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L47-L48

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

theorem PI.WeylForKWork.eMi_ne_ePl (ε : Fin N → Bool) (j : Fin (nMi ε)) (i : Fin (nPl ε)) : eMi ε j ≠ ePl ε i := by sorry
