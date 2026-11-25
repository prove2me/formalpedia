-- Prove2me | Theorems.Thm_PI_FJMD_shapeProd_varMat_ne_zero
-- name    : PI.FJMD.shapeProd_varMat_ne_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T05:28:52.60648+00:00
-- url     : https://prove2.me/theorems/62ec5220-246c-53aa-bcb8-d4a2445a3e0d
-- title:
--   FJMD: shape Prod var Mat ne zero
-- statement:
--   The FJMD construction uses the shape Prod var Mat ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L61-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FockJointMultiplicity/ShapeProdVarMatNeZero.lean#L61-L78

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

theorem PI.FJMD.shapeProd_varMat_ne_zero {p q r s m k : ℕ} (ρ : Fin m → Ix p q) (κ : Fin k → Ix r s)
    (hρ : Function.Injective ρ) (hκ : Function.Injective κ) (α : List ℕ)
    (hm : α.length ≤ m) (hk : α.length ≤ k) : shapeProd (varMat (r := r) (s := s) ρ κ) α ≠ 0 := by sorry
