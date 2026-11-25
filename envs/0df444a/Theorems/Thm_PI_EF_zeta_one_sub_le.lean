-- Prove2me | Theorems.Thm_PI_EF_zeta_one_sub_le
-- name    : PI.EF.zeta_one_sub_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:37.494893+00:00
-- url     : https://prove2.me/theorems/3d6897ff-9668-4f19-86e2-412bbd56feab
-- title:
--   EF: zeta one sub le
-- statement:
--   The EF construction uses the zeta one sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthZeta.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthZeta.lean#L12-L16

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

theorem PI.EF.zeta_one_sub_le {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 5) (h : w ≠ 1) :
    ‖riemannZeta (1 - w)‖ ≤ 6 * ‖w + 1‖ ^ 5 * ‖riemannZeta w‖ := by sorry
