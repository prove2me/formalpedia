-- Prove2me | Theorems.Thm_PI_FJMD_det_vars_ne_zero
-- name    : PI.FJMD.det_vars_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:30:28.566849+00:00
-- url     : https://prove2.me/theorems/8fd19391-7210-4cda-ada7-2a0eff64a116
-- title:
--   FJMD: det vars ne zero
-- statement:
--   The FJMD construction uses the det vars ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L35-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L35-L59

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_JointMultOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_ShapeProdVarMatNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action
open PI PI.FJMD
open PI.FJM

theorem PI.FJMD.det_vars_ne_zero {σ : Type*} {n : ℕ} (f : Fin n × Fin n → σ) (hf : Function.Injective f) :
    (Matrix.of fun i j => (MvPolynomial.X (f (i, j)) : MvPolynomial σ ℂ)).det ≠ 0 := by sorry
