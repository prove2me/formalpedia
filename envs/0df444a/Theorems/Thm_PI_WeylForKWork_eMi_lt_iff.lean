-- Prove2me | Theorems.Thm_PI_WeylForKWork_eMi_lt_iff
-- name    : PI.WeylForKWork.eMi_lt_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:49:18.241191+00:00
-- url     : https://prove2.me/theorems/5c584f15-b73a-4779-9966-68996bfda6c5
-- title:
--   Weyl For KWork: e Mi lt iff
-- statement:
--   The Weyl For KWork construction uses the e Mi lt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L25-L27

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

theorem PI.WeylForKWork.eMi_lt_iff (ε : Fin N → Bool) (i j : Fin (nMi ε)) : eMi ε i < eMi ε j ↔ i < j := by sorry
