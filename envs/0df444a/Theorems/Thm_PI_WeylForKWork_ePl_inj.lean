-- Prove2me | Theorems.Thm_PI_WeylForKWork_ePl_inj
-- name    : PI.WeylForKWork.ePl_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:50:05.231723+00:00
-- url     : https://prove2.me/theorems/83485ab5-0250-4f76-bae0-17af3bc83d1f
-- title:
--   Weyl For KWork: e Pl inj
-- statement:
--   The Weyl For KWork construction uses the e Pl inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L29-L31

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

theorem PI.WeylForKWork.ePl_inj (ε : Fin N → Bool) (i j : Fin (nPl ε)) : ePl ε i = ePl ε j ↔ i = j := by sorry
