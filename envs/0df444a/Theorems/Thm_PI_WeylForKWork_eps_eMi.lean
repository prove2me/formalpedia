-- Prove2me | Theorems.Thm_PI_WeylForKWork_eps_eMi
-- name    : PI.WeylForKWork.eps_eMi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:48:11.941214+00:00
-- url     : https://prove2.me/theorems/7ac59b5d-f18a-4e9c-9df2-984d536ef1f7
-- title:
--   Weyl For KWork: eps e Mi
-- statement:
--   The Weyl For KWork construction uses the eps e Mi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L14-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L14-L15

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

theorem PI.WeylForKWork.eps_eMi (ε : Fin N → Bool) (j : Fin (nMi ε)) : ε (eMi ε j) = false := by sorry
