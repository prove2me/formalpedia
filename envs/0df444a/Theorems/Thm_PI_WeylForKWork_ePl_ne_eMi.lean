-- Prove2me | Theorems.Thm_PI_WeylForKWork_ePl_ne_eMi
-- name    : PI.WeylForKWork.ePl_ne_eMi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:59:13.024395+00:00
-- url     : https://prove2.me/theorems/54f66468-10e5-4d9d-9411-453508c7a5c5
-- title:
--   Weyl For KWork: e Pl ne e Mi
-- statement:
--   The Weyl For KWork construction uses the e Pl ne e Mi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L37-L39

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

theorem PI.WeylForKWork.ePl_ne_eMi (ε : Fin N → Bool) (i : Fin (nPl ε)) (j : Fin (nMi ε)) : ePl ε i ≠ eMi ε j := by sorry
