-- Prove2me | Theorems.Thm_PI_FJMX_colD_X
-- name    : PI.FJMX.colD_X
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:30:05.30435+00:00
-- url     : https://prove2.me/theorems/d4b2d679-19c5-4e1f-b5fd-02f838aa9d52
-- title:
--   FJMX: col D X
-- statement:
--   The FJMX construction uses the col D X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L112-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L112-L123

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_PurElim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistGen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ExistWt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LeadTDerCols
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FJMX
variable {σ : Type*} {m n : ℕ}

theorem PI.FJMX.colD_X (ι : Fin m × Fin n → σ) (hι : Function.Injective ι) (c d : Fin n) (i : Fin m) (j : Fin n) :
    colD ι c d (X (ι (i, j))) = if j = d then X (ι (i, c)) else 0 := by sorry
