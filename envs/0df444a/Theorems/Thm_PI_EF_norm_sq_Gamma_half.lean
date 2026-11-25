-- Prove2me | Theorems.Thm_PI_EF_norm_sq_Gamma_half
-- name    : PI.EF.norm_sq_Gamma_half
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:29:54.482177+00:00
-- url     : https://prove2.me/theorems/d43c4bf3-101b-4d33-a225-3ceb68ad76d3
-- title:
--   EF: norm sq Gamma half
-- statement:
--   The EF construction uses the norm sq Gamma half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthGamma.lean#L28-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthGamma.lean#L28-L43

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma
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
open Complex Filter Set

theorem PI.EF.norm_sq_Gamma_half (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * t) := by sorry
