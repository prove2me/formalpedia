-- Prove2me | Theorems.Thm_PI_EF_norm_L_one_sub_le
-- name    : PI.EF.norm_L_one_sub_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:20.285869+00:00
-- url     : https://prove2.me/theorems/ac96acce-ea65-4458-a8ab-9c8d2b365b4c
-- title:
--   EF: norm L one sub le
-- statement:
--   The EF construction uses the norm L one sub le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthFE.lean#L49-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthFE.lean#L49-L136

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthFE
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
open scoped ZMod
variable {N : ℕ} [NeZero N]

theorem PI.EF.norm_L_one_sub_le {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {w : ℂ}
    (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 5) (h : χ 0 = 0 ∨ w ≠ 1) :
    ‖LFunction χ (1 - w)‖ ≤ 6 * (N : ℝ) ^ 5 * ‖w + 1‖ ^ 5 * ‖LFunction χ⁻¹ w‖ := by sorry
