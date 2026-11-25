-- Prove2me | Theorems.Thm_PI_EF_logDerivHoriz_of
-- name    : PI.EF.logDerivHoriz_of
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:30:06.721239+00:00
-- url     : https://prove2.me/theorems/ff234482-0228-4472-8411-e13c3ce5aa7c
-- title:
--   EF: log Deriv Horiz of
-- statement:
--   The EF construction uses the log Deriv Horiz of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LogDerivBounds.lean#L184-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LogDerivBounds.lean#L184-L194

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LogDerivBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.EF
open Complex DirichletCharacter

theorem PI.EF.logDerivHoriz_of {Cw Cl κ : ℝ} (hCw : 0 ≤ Cw) (hCl : 0 ≤ Cl) (hκ : 0 < κ)
    (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) (hZ : ZeroLocus) :
    LogDerivHoriz κ (4 * Cl + 2 * Cw * κ + 16) := by sorry
