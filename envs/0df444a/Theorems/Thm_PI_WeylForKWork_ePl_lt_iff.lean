-- Prove2me | Theorems.Thm_PI_WeylForKWork_ePl_lt_iff
-- name    : PI.WeylForKWork.ePl_lt_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:49:17.288253+00:00
-- url     : https://prove2.me/theorems/28dd3064-9765-4edd-86ab-3949f2544310
-- title:
--   Weyl For KWork: e Pl lt iff
-- statement:
--   The Weyl For KWork construction uses the e Pl lt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L21-L23

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

theorem PI.WeylForKWork.ePl_lt_iff (ε : Fin N → Bool) (i j : Fin (nPl ε)) : ePl ε i < ePl ε j ↔ i < j := by sorry
