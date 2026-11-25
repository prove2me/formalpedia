-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_cm_mul
-- name    : PI.UnitaryGroupMassFormula.UsCost.DA.cm_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T06:04:12.634798+00:00
-- url     : https://prove2.me/theorems/105745ef-58a3-4c14-a7a3-58752fd05d37
-- title:
--   DA: cm mul
-- statement:
--   The DA construction uses the cm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivA.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivA.lean#L21-L26

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x : X}

theorem PI.UnitaryGroupMassFormula.UsCost.DA.cm_mul {a b c : ℕ} {F : X → Matrix (Fin a) (Fin b) ℂ} {G : X → Matrix (Fin b) (Fin c) ℂ}
    (hF : ContDiffAt ℝ n F x) (hG : ContDiffAt ℝ n G x) : ContDiffAt ℝ n (fun y => F y * G y) x := by sorry
