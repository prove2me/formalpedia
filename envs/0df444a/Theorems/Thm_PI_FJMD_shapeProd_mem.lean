-- Prove2me | Theorems.Thm_PI_FJMD_shapeProd_mem
-- name    : PI.FJMD.shapeProd_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:52:05.554574+00:00
-- url     : https://prove2.me/theorems/6b618e5e-7dfe-41d7-99e3-a8b4c64668b9
-- title:
--   FJMD: shape Prod mem
-- statement:
--   The FJMD construction uses the shape Prod mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L18-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L18-L33

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

theorem PI.FJMD.shapeProd_mem {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (S : Subalgebra R A)
    {m k : ℕ} (M : Matrix (Fin m) (Fin k) A) (α : List ℕ)
    (h : ∀ (i : Fin m) (j : Fin k), i.val < α.length → j.val < α.length → M i j ∈ S) :
    shapeProd M α ∈ S := by sorry
