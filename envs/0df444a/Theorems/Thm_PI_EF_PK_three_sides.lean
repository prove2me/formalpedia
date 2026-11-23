-- Prove2me | Theorems.Thm_PI_EF_PK_three_sides
-- name    : PI.EF.PK.three_sides
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:22:48.567391+00:00
-- url     : https://prove2.me/theorems/1e73e67a-82e0-46ae-b37b-92818d8d6f3f
-- title:
--   PK: three sides
-- statement:
--   The PK construction uses the three sides property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L77-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ExplicitFormula/PerronKernelA.lean#L77-L83

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_GoodHeightExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_RectInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_PerronKernelA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.EF PI.EF.PK
open Complex MeasureTheory intervalIntegral Real

theorem PI.EF.PK.three_sides {L B Tp R : ℂ} (h : I * L = B - Tp + I * R) : ‖L‖ ≤ ‖B‖ + ‖Tp‖ + ‖R‖ := by sorry
