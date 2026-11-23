-- Prove2me | Theorems.Thm_PI_JetsPhW_Low_degree_expXY
-- name    : PI.JetsPhW.Low.degree_expXY
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:37.470998+00:00
-- url     : https://prove2.me/theorems/01606bc7-b9d3-4503-8616-039e3ac3df32
-- title:
--   Low: degree exp XY
-- statement:
--   The Low construction uses the degree exp XY property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L75-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L75-L76

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_CoeffSubstOfDegreeEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.JetsPhW PI.JetsPhW.Low
variable {K : Type*} [CommRing K]

theorem PI.JetsPhW.Low.degree_expXY : Finsupp.degree bivariateExponentMonomial = 2 := by sorry
