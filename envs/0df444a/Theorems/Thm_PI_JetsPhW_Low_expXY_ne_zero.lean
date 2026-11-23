-- Prove2me | Theorems.Thm_PI_JetsPhW_Low_expXY_ne_zero
-- name    : PI.JetsPhW.Low.expXY_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:38.695981+00:00
-- url     : https://prove2.me/theorems/04382b2b-cb7d-4c9a-bbb5-0089d0457a1f
-- title:
--   Low: exp XY ne zero
-- statement:
--   The Low construction uses the exp XY ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L78-L81

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

theorem PI.JetsPhW.Low.expXY_ne_zero : bivariateExponentMonomial ≠ 0 := by sorry
