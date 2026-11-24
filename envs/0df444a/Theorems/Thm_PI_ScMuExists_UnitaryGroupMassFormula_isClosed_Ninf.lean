-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_isClosed_Ninf
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.isClosed_Ninf
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T13:13:37.762807+00:00
-- url     : https://prove2.me/theorems/956c15e0-86fb-4491-a707-69e3fae1860f
-- title:
--   Unitary Group Mass Formula: is Closed Ninf
-- statement:
--   The Unitary Group Mass Formula construction uses the is Closed Ninf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousUMatApply.lean#L213-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousUMatApply.lean#L213-L219

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable (I : Formalism.MainNotions.S.AutInst)
variable {r : ℕ}

theorem PI.ScMuExists.UnitaryGroupMassFormula.isClosed_Ninf (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : IsClosed (Ninf I e z) := by sorry
