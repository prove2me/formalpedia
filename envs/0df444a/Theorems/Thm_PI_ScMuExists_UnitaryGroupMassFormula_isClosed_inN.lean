-- Prove2me | Theorems.Thm_PI_ScMuExists_UnitaryGroupMassFormula_isClosed_inN
-- name    : PI.ScMuExists.UnitaryGroupMassFormula.isClosed_inN
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:40:21.421146+00:00
-- url     : https://prove2.me/theorems/258c8961-db10-52cd-ada3-ad00d01b5416
-- title:
--   Unitary Group Mass Formula: is Closed in N
-- statement:
--   The Unitary Group Mass Formula construction uses the is Closed in N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousUMatApply.lean#L108-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MeasureDecomposition/ContinuousUMatApply.lean#L108-L117

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
variable {n r : ℕ}

theorem PI.ScMuExists.UnitaryGroupMassFormula.isClosed_inN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) :
    IsClosed {g : Matrix (Fin n) (Fin n) ℂ | InN ε e z g} := by sorry
