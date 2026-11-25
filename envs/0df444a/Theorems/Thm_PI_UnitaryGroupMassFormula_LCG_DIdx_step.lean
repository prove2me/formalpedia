-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_LCG_DIdx_step
-- name    : PI.UnitaryGroupMassFormula.LCG.DIdx.step
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:40:16.378402+00:00
-- url     : https://prove2.me/theorems/7cd33ae9-ee09-46f1-9706-831c0dc66bc2
-- title:
--   DIdx: step
-- statement:
--   The DIdx construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/IndexDual.lean#L94-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeCountingBound/IndexDual.lean#L94-L185

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeCountingBound_IndexDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.LCG
open PI.UnitaryGroupMassFormula.LCG.DIdx

theorem PI.UnitaryGroupMassFormula.LCG.DIdx.step (K : Type) [Field K] [NumberField K] (k : ℕ) (X Y : Submodule (𝓞 K) (Fin k → K)) (hXY : X ≤ Y)
    (hne : X.toAddSubgroup.relIndex Y.toAddSubgroup ≠ 0) (x : Fin k → K) (hxY : x ∈ Y) :
    (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≠ 0 ∧
    (dualL (X ⊔ Submodule.span (𝓞 K) {x})).toAddSubgroup.relIndex (dualL X).toAddSubgroup ≤
      X.toAddSubgroup.relIndex (X ⊔ Submodule.span (𝓞 K) {x}).toAddSubgroup := by sorry
