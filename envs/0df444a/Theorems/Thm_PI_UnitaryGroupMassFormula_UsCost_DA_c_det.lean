-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_c_det
-- name    : PI.UnitaryGroupMassFormula.UsCost.DA.c_det
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:51:03.629675+00:00
-- url     : https://prove2.me/theorems/a9a92b1b-9483-41f7-8d53-4afe512ee5f0
-- title:
--   DA: c det
-- statement:
--   The DA construction uses the c det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivA.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivA.lean#L28-L32

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

theorem PI.UnitaryGroupMassFormula.UsCost.DA.c_det {a : ℕ} {F : X → Matrix (Fin a) (Fin a) ℂ} (hF : ContDiffAt ℝ n F x) :
    ContDiffAt ℝ n (fun y => (F y).det) x := by sorry
