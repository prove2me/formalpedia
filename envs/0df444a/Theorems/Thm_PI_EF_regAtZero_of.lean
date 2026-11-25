-- Prove2me | Theorems.Thm_PI_EF_regAtZero_of
-- name    : PI.EF.regAtZero_of
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:29:31.391723+00:00
-- url     : https://prove2.me/theorems/ae7cc9be-7eb2-43be-916f-063825974e42
-- title:
--   EF: reg At Zero of
-- statement:
--   The EF construction uses the reg At Zero of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RegZero.lean#L11-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/RegZero.lean#L11-L170

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RegZero
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
open Complex DirichletCharacter Filter Topology

theorem PI.EF.regAtZero_of {Cw Cl : ℝ} (hW : ZerosWindowWith Cw) (hL : LocalLemma Cl) :
    RegAtZero (Cw + Cl) := by sorry
