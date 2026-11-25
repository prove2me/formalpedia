-- Prove2me | Theorems.Thm_PI_FJMX_leadT_diag
-- name    : PI.FJMX.leadT_diag
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:31:43.641958+00:00
-- url     : https://prove2.me/theorems/e6550c66-3836-40e3-ae0a-1fdc9071ed61
-- title:
--   FJMX: lead T diag
-- statement:
--   The FJMX construction uses the lead T diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L184-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/LeadTDerCols.lean#L184-L210

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

theorem PI.FJMX.leadT_diag (ι : Fin m × Fin m → σ) (hι : Function.Injective ι) (t : ℕ) (ht : t ≤ m) :
    aeval (PI.FJMB.killS (PI.FJMB.offD ι)) (PI.FJM.leadT (blkM ι) t) =
      ∏ i : Fin m, X (ι (i, i)) ^ (if i.val < t then 1 else 0) := by sorry
