-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_cm_conjT
-- name    : PI.UnitaryGroupMassFormula.UsCost.DA.cm_conjT
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:53:38.666898+00:00
-- url     : https://prove2.me/theorems/2bc2b617-d9d5-45a8-8a9b-2bee9d6cf925
-- title:
--   DA: cm conj T
-- statement:
--   The DA construction uses the cm conj T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivA.lean#L53-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivA.lean#L53-L58

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

theorem PI.UnitaryGroupMassFormula.UsCost.DA.cm_conjT {a b : ℕ} {F : X → Matrix (Fin a) (Fin b) ℂ} (hF : ContDiffAt ℝ n F x) :
    ContDiffAt ℝ n (fun y => (F y)ᴴ) x := by sorry
