-- Prove2me | Theorems.Thm_PI_FJMD_det_mem_subalgebra
-- name    : PI.FJMD.det_mem_subalgebra
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:31:20.226209+00:00
-- url     : https://prove2.me/theorems/3a448152-7f2f-4731-b493-6dcb7b16fa8c
-- title:
--   FJMD: det mem subalgebra
-- statement:
--   The FJMD construction uses the det mem subalgebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L11-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L11-L16

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

theorem PI.FJMD.det_mem_subalgebra {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) A) (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by sorry
