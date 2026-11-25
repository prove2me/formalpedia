-- Prove2me | Theorems.Thm_PI_FJMX_bCol_eq_colD
-- name    : PI.FJMX.bCol_eq_colD
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:30:37.933453+00:00
-- url     : https://prove2.me/theorems/af03d0b8-5a62-40f9-8f43-d29ce0c818a3
-- title:
--   FJMX: b Col eq col D
-- statement:
--   The FJMX construction uses the b Col eq col D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L94-L97

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

theorem PI.FJMX.bCol_eq_colD (ι : Fin m × Fin n → σ) (c d : Fin n) (f : MvPolynomial σ ℂ) :
    PI.FJM.bCol ι c d f = colD ι c d f := by sorry
