-- Prove2me | Theorems.Thm_PI_EF_zeta_left
-- name    : PI.EF.zeta_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:14.438798+00:00
-- url     : https://prove2.me/theorems/cc84098e-7538-5e2a-8090-037ef60e2630
-- title:
--   EF: zeta left
-- statement:
--   The EF construction uses the zeta left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthZeta.lean#L47-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthZeta.lean#L47-L91

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthFE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthZeta
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

theorem PI.EF.zeta_left (hZ : PI.ZetaBoundRight) {s : ℂ} (h1 : -4 ≤ s.re) (h2 : s.re < 1 / 2)
    (h3 : 1 / 2 ≤ ‖s‖) : ‖(s - 1) * riemannZeta s‖ ≤ 48114 * (|s.im| + 2) ^ 7 := by sorry
