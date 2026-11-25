-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_deg_lin
-- name    : PI.UnitaryGroupMassFormula.UsCompose.deg_lin
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T06:03:35.943661+00:00
-- url     : https://prove2.me/theorems/cf9ef08e-5f80-49e8-8b01-b16396f8e0fc
-- title:
--   Us Compose: deg lin
-- statement:
--   The Us Compose construction uses the deg lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/DegPderivMul.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/DegPderivMul.lean#L19-L22

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

theorem PI.UnitaryGroupMassFormula.UsCompose.deg_lin {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) (i : Vr N) : (lin X i).totalDegree ≤ 1 := by sorry
