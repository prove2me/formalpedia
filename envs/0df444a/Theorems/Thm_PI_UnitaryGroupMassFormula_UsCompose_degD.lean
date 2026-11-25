-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_degD
-- name    : PI.UnitaryGroupMassFormula.UsCompose.degD
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T06:14:13.000969+00:00
-- url     : https://prove2.me/theorems/e2d8c4be-8412-4d1b-8717-d329f1846cbf
-- title:
--   Us Compose: deg D
-- statement:
--   The Us Compose construction uses the deg D property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/DegPderivMul.lean#L41-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/DegPderivMul.lean#L41-L42

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_StepOne
import Definitions.Def_Lemmata_PartialDerivativeDegree_PderivTdSuccLe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_DegPderivMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCompose
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.U

theorem PI.UnitaryGroupMassFormula.UsCompose.degD (k j ρ : ℕ) : (qD k j ρ).totalDegree ≤ j ∧ (qDb k j ρ).totalDegree ≤ j := by sorry
