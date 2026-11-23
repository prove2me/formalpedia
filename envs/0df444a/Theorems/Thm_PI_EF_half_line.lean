-- Prove2me | Theorems.Thm_PI_EF_half_line
-- name    : PI.EF.half_line
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:54.739295+00:00
-- url     : https://prove2.me/theorems/cd4c8b54-1ec1-4fb5-9e7c-291be18ad59d
-- title:
--   EF: half line
-- statement:
--   The EF construction uses the half line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthGamma.lean#L45-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/LGrowthGamma.lean#L45-L66

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

theorem PI.EF.half_line (t : ℝ) :
    ‖Complex.Gamma (1 / 2 + t * I)‖ * Real.exp (Real.pi / 2 * |t|) ≤ 3 := by sorry
