-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_deg_CX
-- name    : PI.UnitaryGroupMassFormula.UsCompose.deg_CX
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T15:49:49.011688+00:00
-- url     : https://prove2.me/theorems/ba1366ee-6ff5-4bd3-b857-5d6209835711
-- title:
--   Us Compose: deg CX
-- statement:
--   The Us Compose construction uses the deg CX property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/DegPderivMul.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/DegPderivMul.lean#L16-L17

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

theorem PI.UnitaryGroupMassFormula.UsCompose.deg_CX {σ : Type*} (a : ℂ) (v : σ) : (C a * X v : MvPolynomial σ ℂ).totalDegree ≤ 1 := by sorry
