-- Prove2me | Theorems.Thm_PI_FJMX_shapeProd_diag
-- name    : PI.FJMX.shapeProd_diag
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:30:19.80005+00:00
-- url     : https://prove2.me/theorems/2d785a5a-7944-4325-bb8b-8310029ff7a4
-- title:
--   FJMX: shape Prod diag
-- statement:
--   The FJMX construction uses the shape Prod diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L212-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L212-L246

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
variable {σ : Type*} {m : ℕ}

theorem PI.FJMX.shapeProd_diag (ι : Fin m × Fin m → σ) (hι : Function.Injective ι) (α : Fin m → ℕ) (hα : Antitone α) :
    aeval (PI.FJMB.killS (PI.FJMB.offD ι)) (PI.FJM.shapeProd (blkM ι) (List.ofFn α)) =
      ∏ i, X (ι (i, i)) ^ α i := by sorry
