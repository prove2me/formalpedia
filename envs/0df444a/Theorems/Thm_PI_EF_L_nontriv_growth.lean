-- Prove2me | Theorems.Thm_PI_EF_L_nontriv_growth
-- name    : PI.EF.L_nontriv_growth
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:29:12.709792+00:00
-- url     : https://prove2.me/theorems/ded39e02-173e-436e-975c-37af6c0f0dd6
-- title:
--   EF: L nontriv growth
-- statement:
--   The EF construction uses the L nontriv growth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthMain.lean#L33-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthMain.lean#L33-L74

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthFE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthMain
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
variable {N : ℕ} [NeZero N]

theorem PI.EF.L_nontriv_growth (hB : PI.LBoundRight) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {s : ℂ} (h1 : -4 ≤ s.re) (h2 : s.re ≤ 8) :
    ‖LFunction χ s‖ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := by sorry
