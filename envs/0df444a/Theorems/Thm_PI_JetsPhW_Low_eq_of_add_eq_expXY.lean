-- Prove2me | Theorems.Thm_PI_JetsPhW_Low_eq_of_add_eq_expXY
-- name    : PI.JetsPhW.Low.eq_of_add_eq_expXY
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:09:40.58979+00:00
-- url     : https://prove2.me/theorems/7ef0ccca-d86e-5d5c-ba5d-a45b7e4bdc42
-- title:
--   Low: eq of add eq exp XY
-- statement:
--   The Low construction uses the eq of add eq exp XY property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L88-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/CoeffSubstOfDegreeEqOne.lean#L88-L108

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

theorem PI.JetsPhW.Low.eq_of_add_eq_expXY {x y : Fin 2 →₀ ℕ} (hxy : x + y = bivariateExponentMonomial) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x = E0 ∧ y = E1) ∨ (x = E1 ∧ y = E0) := by sorry
