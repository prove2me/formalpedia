-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_deg_det
-- name    : PI.UnitaryGroupMassFormula.UsCompose.deg_det
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:52:47.891945+00:00
-- url     : https://prove2.me/theorems/7073d71b-d091-483f-a1b1-a7ed911a8876
-- title:
--   Us Compose: deg det
-- statement:
--   The Us Compose construction uses the deg det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/DegPderivMul.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentComposition/DegPderivMul.lean#L28-L39

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

theorem PI.UnitaryGroupMassFormula.UsCompose.deg_det {σ : Type*} {n : ℕ} (M : Matrix (Fin n) (Fin n) (MvPolynomial σ ℂ))
    (hM : ∀ a b, (M a b).totalDegree ≤ 1) : M.det.totalDegree ≤ n := by sorry
