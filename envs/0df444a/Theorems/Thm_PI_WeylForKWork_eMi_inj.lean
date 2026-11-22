-- Prove2me | Theorems.Thm_PI_WeylForKWork_eMi_inj
-- name    : PI.WeylForKWork.eMi_inj
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:49:35.042826+00:00
-- url     : https://prove2.me/theorems/64b6d6ac-5db8-4d46-b0e4-b0e399e9c36f
-- title:
--   Weyl For KWork: e Mi inj
-- statement:
--   The Weyl For KWork construction uses the e Mi inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L33-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeylFormulaCompact/Formula.lean#L33-L35

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

theorem PI.WeylForKWork.eMi_inj (ε : Fin N → Bool) (i j : Fin (nMi ε)) : eMi ε i = eMi ε j ↔ i = j := by sorry
